import Tools.ShippingGateTypedWalk

variable {tenv : Lean.Environment}

/-! # Gate-route parents: the three walks over a call with ANY spine split (worker N, round 16)

WRITTEN, NOT BUILT.

The round-11/13/14 instance nodes `desW_inst`, `namW_inst`, `typW_inst`
(and the shared lowering lemma `instUncached_namW`) are stated for
`instEN mn lvls dom argsE` whose PORT arguments are `argsE` — the callee's
inputs are matched against the spine minus its FIRST argument (a leading
domain). For a callee without a domain binder (`pick sel x`: spine
`[sel, x]`, both ports) that reading is wrong: the compiler's last-#ports
rule connects `drop (length - #ports)` of the spine.

Here the same four lemmas for a call `instEN mn lvls dom rest` whose spine
`dom :: rest` is split as `pre ++ argsE` with `argsE` the ports
(`hsp`, `hlen : mc.inputs.length = argsE.length`): the arity guard and the
`drop` are those of `Tools.ShippingInstanceMeaningP.instUncached_shapeE`.
The old lemmas are kept (they are the case `pre = [dom]`).

* `instUncached_namWE` — `instUncached_namW` (a copy of its proof) at any split;
* `desW_instE`, `namW_instE`, `typW_instE` — the three instance nodes (copies
  of the proofs of `desW_inst`, `namW_inst`, `typW_inst`; the design node now
  reads the fresh case of `instUncached_namWE`, which has two more facts). -/
namespace Tools.ShippingGateParentRun

set_option linter.unusedSectionVars false

section walkE
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

/-- **The uncached instance lowering at any split of the spine** (`instUncached_namW`,
a copy of its proof): the spine `dom :: rest` is `pre ++ argsE`, the callee's
inputs are matched with `argsE` (the compiler's last-#ports rule). -/
theorem instUncached_namWE (L : RefLaws mref cref) {D : Nat} {rec : TranslateFn}
    (hrec : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D) (rec e hint top named))
    {ctx : CompilerState} {mn : Name}
    {mc : Sparkle.IR.AST.Module} {dc : Sparkle.IR.AST.Design} {so : Sparkle.IR.AST.Port}
    {lvls : List Level} {dom : Lean.Expr} {rest pre argsE : List Lean.Expr}
    {hint : String} {top named : Bool} {s t : CircuitState} {w : String}
    {w0 w1 : Void IO.RealWorld}
    (hdc : dc.modules = [])
    (hnoclk : ∀ p ∈ mc.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hsp : dom :: rest = pre ++ argsE)
    (hlen : mc.inputs.length = argsE.length)
    (hw0 : InvV L w0) (hd0 : L.dval w0 = D)
    (run : RunsC (translateInstanceUncachedWith rec mn mc dc so
      (instEN mn lvls dom rest) hint top named) ctx s mctx mref cctx cref w0 (w, t) w1) :
    ∃ (d' : Sparkle.IR.AST.Design) (conns : List (String × Sparkle.IR.AST.Expr))
      (sA : CircuitState) (wa wb : Void IO.RealWorld),
      InvV L wa ∧ L.dval wa = D ∧ InvV L w1 ∧ L.dval w1 = D ∧ SubMap (L.val wb) (L.val w1) ∧
      RunsC (instArgs rec [] (mc.inputs.zip argsE) 0) ctx { s with design := d' }
        mctx mref cctx cref wa (conns, sA) wb ∧
      (∀ x ∈ d'.modules, x ∈ s.design.modules ∨ x = mc) ∧
      (∀ x ∈ s.design.modules, x ∈ d'.modules) ∧ (∃ x ∈ d'.modules, x.name = mc.name) ∧
      ((instHitValid s.translateRecord (instEN mn lvls dom rest) w = true ∧ t = sA) ∨
       (w = (CircuitM.makeWire hint so.ty named sA).1 ∧
        ∃ iname : String,
         iname = (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).1 ∧
         t = { (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2 with
           module := (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module.addStmt
             (.inst mc.name iname (conns.reverse ++ [(so.name, .ref w)])) })) := by
  rw [instanceUncached_run] at run
  obtain ⟨cs0, sG, wg, hget0, k1⟩ := RunsC.bind (c := (get : CompilerM CircuitState)) run
  obtain ⟨hcs0, hsG, hwg⟩ := runsC_get hget0
  rw [hcs0, hsG, hwg] at k1
  rw [hdc] at k1
  obtain ⟨u0, sA0, wA0, hAdd0, k2⟩ := RunsC.bind (c := instAddModules _ []) k1
  have hAdd0' : RunsC (Pure.pure () : CompilerM Unit) ctx s mctx mref cctx cref w0 (u0, sA0)
      wA0 := hAdd0
  obtain ⟨hp0, hwA0⟩ := RunsC.pure hAdd0'
  rw [(Prod.mk.inj hp0).2, hwA0] at k2
  obtain ⟨uR, sB, wR, hReg, k3⟩ := RunsC.bind (c := instRegisterChild _ mc) k2
  obtain ⟨hwR, hdR, -⟩ := keepsW L (fun L' => by vc) hw0 hd0 hReg
  obtain ⟨d', hsB, hdes1, hdes2, hdes3⟩ := instRegisterChild_des (runsCReturns hReg)
  obtain ⟨conns0, sC, wC, hClk, k4⟩ := RunsC.bind (c := instClkRst [] mc.inputs) k3
  obtain ⟨hwC, hdC, -⟩ :=
    keepsW L (fun L' => instClkRst_keepsC L' D mc.inputs []) hwR hdR hClk
  obtain ⟨hconns0, hsC⟩ := instClkRst_skip hnoclk (runsCReturns hClk)
  have hfl : mc.inputs.filter (fun p => p.name != "clk" && p.name != "rst") = mc.inputs := by
    rw [List.filter_eq_self]
    intro p hp
    obtain ⟨h1, h2⟩ := hnoclk p hp
    simp [bne, h1, h2]
  rw [hfl, instEN_spineArgs, hsp] at k4
  obtain ⟨uG, sH, wH, hGuard, k5⟩ := RunsC.bind (c := instArityCheck mn _ _) k4
  unfold instArityCheck at hGuard
  rw [if_neg (by
    rw [List.length_append, hlen]
    exact Nat.not_lt.mpr (Nat.le_add_left _ _))] at hGuard
  obtain ⟨hpG, hwH⟩ := RunsC.pure hGuard
  have hsH : sH = sC := (Prod.mk.inj hpG).2
  have hdrop : (pre ++ argsE).drop ((pre ++ argsE).length - mc.inputs.length) = argsE := by
    rw [hlen, List.length_append, Nat.add_sub_cancel]
    exact List.drop_left
  rw [hdrop, hconns0] at k5
  obtain ⟨conns, sF, wb, hArgs, k6⟩ := RunsC.bind (c := instArgs _ _ _ 0) k5
  rw [hsH, hsC, hsB, hwH] at hArgs
  obtain ⟨hwb, hdb, -⟩ :=
    keepsW L (fun L' => instArgs_keepsC L' D rec (hrec L') _ _ _) hwC hdC hArgs
  obtain ⟨hw1, hd1, hsub6⟩ := keepsW L (fun L' => by vc) hwb hdb k6
  refine ⟨d', conns, sF, wC, wb, hwC, hdC, hw1, hd1, hsub6, hArgs, hdes1, hdes2, hdes3, ?_⟩
  have k6R := runsCReturns k6
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6R
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  have hsQ := Returns.liftMetaM hCacheRead
  cases hhit : (cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
      (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}").filter
      (instHitValid s.translateRecord (instEN mn lvls dom rest)) with
  | some cw =>
    rw [hhit] at k8
    obtain ⟨hw, ht⟩ := Returns.pure k8
    left
    refine ⟨?_, by rw [ht, hsQ, hsP2]⟩
    rw [hw]
    cases hget : cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
        (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}" with
    | none => rw [hget] at hhit; cases hhit
    | some c0 =>
      rw [hget] at hhit
      by_cases hv : instHitValid s.translateRecord (instEN mn lvls dom rest) c0 = true
      · have : (some c0 : Option String) = some cw := by
          simpa [Option.filter, hv] using hhit
        cases this
        exact hv
      · simp [Option.filter, hv] at hhit
  | none =>
    rw [hhit] at k8
    simp only [] at k8
    obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire hint _ named) k8
    obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
    obtain ⟨uP, sV, hPut, k10⟩ :=
      Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
    have hsV := Returns.liftMetaM hPut
    obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
    obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
    obtain ⟨uL, sL, hLink, k11⟩ := Returns.bind (m := instLinkCheck _ _ _) k11
    obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
    rw [hsL] at k11
    obtain ⟨uE, sI, hEmit, k12⟩ :=
      Returns.bind (m := CompilerM.emitInstance mc.name _ _) k11
    have hsI := emitInstanceC_returns hEmit
    obtain ⟨hwEq, ht⟩ := Returns.pure k12
    right
    refine ⟨?_, instName, ?_, ?_⟩
    · (rw [hwEq, houtW, hsQ, hsP2]) <;> simp
    · (rw [hinstName, hsV, hsW, hsQ, hsP2]) <;> simp
    · rw [ht, hsI, hsN, hsV, hsW, hsQ, hsP2, hwEq]
      simp

/-- **An instance call at any split of its spine** (`desW_inst`, a copy of its
proof): the ports are `argsE`, `dom :: rest = pre ++ argsE`. -/
theorem desW_instE (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {N : String} {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr}
    {rest pre argsE : List Lean.Expr}
    (hsp : dom :: rest = pre ++ argsE)
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom rest) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    (hleaf : ∀ y : Res, mF.get? mn = some y → InstLeafOk G argsE.length y)
    (hargs : ∀ k (hk : k < argsE.length), ∃ hi : Bool,
      DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N (argsE[k]'hk) hi) :
    DesW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G N
      (instEN mn lvls dom rest) true := by
  intro mctx cctx hint top named s t w w0 w1 hw hd hsub hr hok
  obtain ⟨y, wm, -, hget, hwm, hdm, hrA⟩ :=
    inst_leaf_runsW (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
  obtain ⟨hG, hdc, hnoclk, hlen, o, k, houts, hk⟩ := hleaf y (hsub mn y hget)
  have hrecK : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D)
        (translateFuelFix (translateStep tenv) fuel e hint top named) :=
    fun L' => fuelRec_keepsC (tenv := tenv) L' D (childKeeps L' D (fun h => absurd h hD)) fuel
  -- the continuation at a one-output child is the validated wrapper
  have hr' : RunsC (translateControlCachedWith
      (translateInstanceUncachedWith (translateFuelFix (translateStep tenv) fuel) mn y.1 y.2
        ⟨o, .bitVector k⟩) (instEN mn lvls dom rest) hint top named) ctx s
      mctx mref cctx cref wm (w, t) w1 := by
    unfold Tools.ShippingChildInv.armCont at hrA
    rw [houts] at hrA
    exact hrA
  rcases controlCached_runsW L hwm hdm hr' with hit | ⟨sm, wa, wb, hwa, hda, lowerRun, recordRun⟩
  · -- a validated hit of the expression cache: the recorded expression's
    -- translation already emitted an instance
    have hlk := cacheLookupValidated_returns hit
    rw [hlk.1]
    exact ⟨hok, DGrows.refl _, fun _ => hok.recs _ _ (hlk.2 _ rfl)⟩
  · obtain ⟨d', conns, sA, wc, wd, hwc, hdc', hwb, hdb, subD, hArgs, hdes1, hdes2, hdes3,
      hcase⟩ := instUncached_namWE L hrecK hdc hnoclk hsp hlen hwa hda lowerRun
    obtain ⟨-, -, subR⟩ := keepsW L (fun L' => recordTranslation_keepsC L' D
      (instEN mn lvls dom rest) w (!named && !(instEN mn lvls dom rest).isFVar && !top))
      hwb hdb recordRun
    have hpairs : ∀ j (hj : j < (y.1.inputs.zip argsE).length), ∃ hi : Bool,
        DesW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G N
          ((y.1.inputs.zip argsE)[j]'hj).2 hi := by
      intro j hj
      have hjA : j < argsE.length := by
        simp only [List.length_zip] at hj
        omega
      have : ((y.1.inputs.zip argsE)[j]'hj).2 = argsE[j]'hjA := by simp
      rw [this]
      exact hargs j hjA
    -- the design after the registration
    have dS : DOk G N { s with design := d' } := by
      refine hok.design d' (fun x hx => ?_) hdes2
      rcases hdes1 x hx with hx' | rfl
      · exact hok.mods x hx'
      · exact hG
    have gS : DGrows s { s with design := d' } := ⟨hdes2, fun _ h => h⟩
    obtain ⟨-, hAr⟩ := instArgs_desW L hD fuel (y.1.inputs.zip argsE) [] 0 conns
      { s with design := d' } sA wc wd hpairs hwc hdc' (sub_trans subD (sub_trans subR hsub))
      hArgs
    obtain ⟨dA, gA⟩ := hAr dS
    have gSA : DGrows s sA := gS.trans gA
    have hrefs := instArgs_refs (y.1.inputs.zip argsE) [] 0 conns _ sA
      (fun c hc => by simp at hc) (runsCReturns hArgs)
    have hrecE := recordTranslation_returns (runsCReturns recordRun)
    rw [hrecE]
    rcases hcase with ⟨hvalid, hsm⟩ | ⟨-, iname, -, hsm⟩
    · -- a hit of the instance dedupe cache
      have hasS : HasInst s.module.body := hok.recs _ _ (instHitValid_recordD hvalid)
      have hasA : HasInst sA.module.body := gSA.hasInst hasS
      rw [hsm]
      exact ⟨dA.record _ _ hasA, gSA.trans (dGrows_record _ _ _), fun _ => hasA⟩
    · -- a fresh wire and one instance statement
      have dW := dA.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
        (Or.inr ⟨k, hk, rfl⟩)
      have gW := dGrows_makeWire sA hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
      have dN := dW.freshName s!"inst_{y.1.name}" false
      have gN := dGrows_freshName
        (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2
        s!"inst_{y.1.name}" false
      have hX : ∃ x ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
            sA).2).2.design.modules, x.name = y.1.name := by
        obtain ⟨x, hx, hxn⟩ := hdes3
        exact ⟨x, gN.1 x (gW.1 x (gA.1 x hx)), hxn⟩
      have hcs : ∀ c ∈ conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)],
          ∃ x, c.2 = Sparkle.IR.AST.Expr.ref x := by
        intro c hc
        rcases List.mem_append.mp hc with h1 | h1
        · exact hrefs c (List.mem_reverse.mp h1)
        · rw [List.mem_singleton.mp h1]
          exact ⟨w, rfl⟩
      have dI := dN.addInst (i := iname) hcs hX
      have gI := dGrows_addInst
        (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2
        y.1.name iname
        (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)])
      have hasI : HasInst ({ (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2 with
          module := (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.addStmt
            (.inst y.1.name iname (conns.reverse ++
              [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name,
                Sparkle.IR.AST.Expr.ref w)])) } : CircuitState).module.body :=
        ⟨_, _, _, List.mem_cons_self⟩
      rw [hsm]
      exact ⟨dI.record _ _ hasI,
        (((gSA.trans gW).trans gN).trans gI).trans (dGrows_record _ _ _), fun _ => hasI⟩

/-- **A named instance call at any split of its spine** (`namW_inst`, a copy of
its proof). -/
theorem namW_instE (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {I : List String} {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr}
    {rest pre argsE : List Lean.Expr}
    (hsp : dom :: rest = pre ++ argsE)
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom rest) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    (hleaf : ∀ y : Res, mF.get? mn = some y → InstLeafOk2 G argsE.length y)
    (hargs : ∀ k (hk : k < argsE.length),
      NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I (argsE[k]'hk)) :
    NamW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G I
      (instEN mn lvls dom rest) := by
  intro mctx cctx hint top named s t w w0 w1 hw hd hsub hr hok
  obtain ⟨y, wm, -, hget, hwm, hdm, hrA⟩ :=
    inst_leaf_runsW (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
  obtain ⟨⟨hG, hdc, hnoclk, hlen, o, k, houts, hk⟩, hoin⟩ := hleaf y (hsub mn y hget)
  have hrecK : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D)
        (translateFuelFix (translateStep tenv) fuel e hint top named) :=
    fun L' => fuelRec_keepsC (tenv := tenv) L' D (childKeeps L' D (fun h => absurd h hD)) fuel
  have hr' : RunsC (translateControlCachedWith
      (translateInstanceUncachedWith (translateFuelFix (translateStep tenv) fuel) mn y.1 y.2
        ⟨o, .bitVector k⟩) (instEN mn lvls dom rest) hint top named) ctx s
      mctx mref cctx cref wm (w, t) w1 := by
    unfold Tools.ShippingChildInv.armCont at hrA
    rw [houts] at hrA
    exact hrA
  rcases controlCached_runsW L hwm hdm hr' with hit | ⟨sm, wa, wb, hwa, hda, lowerRun, recordRun⟩
  · have hlk := cacheLookupValidated_returns hit
    rw [hlk.1]
    exact ⟨hok, NGrows.refl _, PendN.refl, Or.inr (hok.recs _ _ (hlk.2 _ rfl))⟩
  · obtain ⟨d', conns, sA, wc, wd, hwc, hdc', hwb, hdb, subD, hArgs, hdes1, hdes2, hdes3,
      hcase⟩ := instUncached_namWE L hrecK hdc hnoclk hsp hlen hwa hda lowerRun
    obtain ⟨-, -, subR⟩ := keepsW L (fun L' => recordTranslation_keepsC L' D
      (instEN mn lvls dom rest) w (!named && !(instEN mn lvls dom rest).isFVar && !top))
      hwb hdb recordRun
    have hpairs : ∀ j (hj : j < (y.1.inputs.zip argsE).length),
        NamW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G I
          ((y.1.inputs.zip argsE)[j]'hj).2 := by
      intro j hj
      have hjA : j < argsE.length := by
        simp only [List.length_zip] at hj
        omega
      have : ((y.1.inputs.zip argsE)[j]'hj).2 = argsE[j]'hjA := by simp
      rw [this]
      exact hargs j hjA
    have nS : NOk G I { s with design := d' } := hok.design d'
    obtain ⟨-, hAr⟩ := instArgs_namW L hD fuel (y.1.inputs.zip argsE) [] 0 conns
      { s with design := d' } sA wc wd hpairs hwc hdc' (sub_trans subD (sub_trans subR hsub))
      hArgs
    obtain ⟨nA, gA, pA, hmapA, hrefsA⟩ := hAr nS (fun c hc => by simp at hc)
    have gSA : NGrows s sA := gA
    have pSA : PendN I s sA := fun x hx => pA x hx
    have hrecE := recordTranslation_returns (runsCReturns recordRun)
    rw [hrecE]
    rcases hcase with ⟨hvalid, hsm⟩ | ⟨hwm', iname, hiname, hsm⟩
    · -- a hit of the instance dedupe cache: a wire some statement mentions
      have hretA : ∃ st ∈ sA.module.body, w ∈ stmtNamesN st := by
        obtain ⟨st, hst, hw'⟩ := hok.recs _ _ (instHitValid_recordD hvalid)
        exact ⟨st, gSA.2.1 st hst, hw'⟩
      rw [hsm]
      exact ⟨nA.record _ _ hretA, gSA.trans (nGrows_record _ _ _), pend_record pSA _ _,
        Or.inr hretA⟩
    · -- a fresh wire, a fresh instance name, one instance statement
      have hspecW := CircuitM.makeWire_spec hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty
        named sA
      have hwNot : sA.usedNames.contains w = false := by
        rw [hwm']
        exact hspecW.1
      have hwUsedW : (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
          sA).2.usedNames.contains w = true := by
        rw [hspecW.2.1, hwm']
        simp [Std.HashSet.contains_insert]
      have hwWire : w ∈ (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
          sA).2.module.wires.map (·.name) := by
        rw [hwm']
        exact wire_makeWire hint _ named sA
      have hwI : w ∉ I := fun hI => by
        have := nA.inU w hI
        rw [hwNot] at this
        cases this
      have hwB : ∀ st ∈ sA.module.body, w ∉ stmtNamesN st := fun st hst hx => by
        have := nA.nmU st hst w hx
        rw [hwNot] at this
        cases this
      have nW := nA.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
      have gW := nGrows_makeWire sA hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
      have nN := nW.freshName s!"inst_{y.1.name}" false
      have gN := nGrows_freshName
        (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2
        s!"inst_{y.1.name}" false
      have hspecN := CircuitM.freshName_spec s!"inst_{y.1.name}" false
        (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2
      -- the instance name
      have hiNot : iname ∉ Tools.ShippingHierState.instNames
          (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.body := by
        rw [hspecN.2.2, hiname]
        intro hm
        obtain ⟨mn', cs', hm'⟩ := mem_instNamesN hm
        have := nW.iU _ _ _ hm'
        rw [hspecN.1] at this
        cases this
      have hiU : (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
            sA).2).2.usedNames.contains iname = true := by
        rw [hspecN.2.1, hiname]
        simp [Std.HashSet.contains_insert]
      -- the connections, keyed by the callee's inputs
      have hz : (y.1.inputs.zip argsE).map (fun q => q.1.name) = y.1.inputs.map (·.name) := by
        have h1 : (y.1.inputs.zip argsE).map (fun q => q.1.name) =
            ((y.1.inputs.zip argsE).map Prod.fst).map (·.name) := by
          rw [List.map_map]
          try rfl
        have hle : y.1.inputs.length ≤ argsE.length := by omega
        rw [h1, List.map_fst_zip (l₁ := y.1.inputs) (l₂ := argsE) hle]
      have hmapIns : conns.reverse.map Prod.fst = y.1.inputs.map (·.name) := by
        rw [List.map_reverse, hmapA, List.map_nil, List.append_nil, List.reverse_reverse, hz]
      have hrefsW : ∀ c ∈ conns.reverse, ∃ a, c.2 = Sparkle.IR.AST.Expr.ref a ∧ a ≠ w := by
        intro c hc
        obtain ⟨a, ha, hra⟩ := hrefsA c (List.mem_reverse.mp hc)
        refine ⟨a, ha, fun he => ?_⟩
        have := hra.used nA
        rw [he, hwNot] at this
        cases this
      have hoin' : o ∉ y.1.inputs.map (·.name) :=
        hoin ⟨o, .bitVector k⟩ (by rw [houts]; exact List.mem_singleton_self _)
      have hconn : ConnOkN y.1 (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)]) :=
        ⟨conns.reverse, o, k, w, houts, rfl, hmapIns, hrefsW, hoin'⟩
      -- the names of the instance statement
      have hnames : ∀ x ∈ stmtNamesN (.inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)])),
          x = w ∨ RetN I sA x := by
        intro x hx
        rw [stmtNamesN_inst] at hx
        obtain ⟨c, hc, hcx⟩ := List.mem_filterMap.mp hx
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨a, ha, hra⟩ := hrefsA c (List.mem_reverse.mp hc)
          rw [connRefN_of ha] at hcx
          rw [← Option.some.inj hcx]
          exact Or.inr hra
        · rw [List.mem_singleton.mp hc] at hcx
          have h0 : connRefN ((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name,
              Sparkle.IR.AST.Expr.ref w) = some w := rfl
          rw [h0] at hcx
          exact Or.inl (Option.some.inj hcx).symm
      have hU : ∀ x ∈ stmtNamesN (.inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)])),
          (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.usedNames.contains x = true := by
        intro x hx
        rcases hnames x hx with rfl | hra
        · exact gN.1 _ hwUsedW
        · exact gN.1 _ (gW.1 _ (hra.used nA))
      have hwr : ∀ x, WritesN (.inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)])) x →
          (∀ S ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.body, x ∉ stmtNamesN S) ∧
          x ∈ (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.wires.map (·.name) ∧ x ∉ I := by
        intro x hx
        rw [writesN_inst hx]
        refine ⟨?_, ?_, hwI⟩
        · rw [hspecN.2.2, hspecW.2.2.1]
          exact hwB
        · rw [hspecN.2.2]
          exact hwWire
      have nI := nN.addInst y.1 hG rfl hconn hU hiU hiNot hwr
      have gI := nGrows_addStmt (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2
        (.inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)]))
      have gSN : NGrows s (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2 :=
        (gSA.trans gW).trans gN
      have pSN : PendN I s (CircuitM.freshName s!"inst_{y.1.name}" false
          (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named sA).2).2 :=
        pSA.trans gSA (PendN.of_body (fun st hst => by
          rw [hspecN.2.2, hspecW.2.2.1] at hst
          exact hst))
      have pI := pend_addStmt (st0 := .inst y.1.name iname (conns.reverse ++
          [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name, Sparkle.IR.AST.Expr.ref w)]))
        (fun x hx hxn => by
          have hxA : FreshN I sA x := pSA.fresh gSA hx
          rcases hnames x hxn with rfl | hra
          · have := hxA.1
            rw [hwNot] at this
            cases this
          · exact hra.ne hxA rfl) pSN
      have hretI : ∃ st ∈ ({ (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2 with
          module := (CircuitM.freshName s!"inst_{y.1.name}" false
            (CircuitM.makeWire hint (⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).ty named
              sA).2).2.module.addStmt
            (.inst y.1.name iname (conns.reverse ++
              [((⟨o, .bitVector k⟩ : Sparkle.IR.AST.Port).name,
                Sparkle.IR.AST.Expr.ref w)])) } : CircuitState).module.body,
          w ∈ stmtNamesN st :=
        ⟨_, List.mem_cons_self,
          mem_stmtNamesN_inst (List.mem_append_right _ (List.mem_singleton_self _))⟩
      rw [hsm]
      exact ⟨nI.record _ _ hretI, (gSN.trans gI).trans (nGrows_record _ _ _),
        pend_record pI _ _, Or.inr hretI⟩

/-- **A typed instance call at any split of its spine** (`typW_inst`, a copy of
its proof): the port arguments `argsE` have the widths of the callee's input
ports. -/
theorem typW_instE (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {G : Sparkle.IR.AST.Module → Prop}
    {Ip : List Sparkle.IR.AST.Port} {τ : Lean.Expr → Nat}
    {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr}
    {rest pre argsE : List Lean.Expr}
    (hsp : dom :: rest = pre ++ argsE)
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom rest) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    (hleaf : ∀ y : Res, mF.get? mn = some y → InstLeafOk2 G argsE.length y)
    (hws : ∀ y : Res, mF.get? mn = some y →
      (∀ pe ∈ y.1.inputs.zip argsE, τ pe.2 = pe.1.ty.bitWidth) ∧
      ∀ p ∈ y.1.outputs, p.ty.bitWidth = τ (instEN mn lvls dom rest))
    (hargs : ∀ a ∈ argsE,
      TypW L mF D (translateFuelFix (translateStep tenv) fuel) ctx G Ip τ a) :
    TypW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx G Ip τ
      (instEN mn lvls dom rest) := by
  intro mctx cctx hint top named s t w w0 w1 hw hd hsub hr hok
  obtain ⟨y, wm, -, hget, hwm, hdm, hrA⟩ :=
    inst_leaf_runsW (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
  have hyF : mF.get? mn = some y := hsub mn y hget
  obtain ⟨⟨hG, hdc, hnoclk, hlen, o, k, houts, hk⟩, hoin⟩ := hleaf y hyF
  obtain ⟨hwsIn, hwsOut⟩ := hws y hyF
  have hkτ : k = τ (instEN mn lvls dom rest) :=
    hwsOut ⟨o, .bitVector k⟩ (by rw [houts]; exact List.mem_singleton_self _)
  have hrecK : ∀ (L' : RefLaws mref cref) (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context)
      (e : Lean.Expr) (hint : String) (top named : Bool),
      KeepsC mctx mref cctx cref (J L' D)
        (translateFuelFix (translateStep tenv) fuel e hint top named) :=
    fun L' => fuelRec_keepsC (tenv := tenv) L' D (childKeeps L' D (fun h => absurd h hD)) fuel
  have hr' : RunsC (translateControlCachedWith
      (translateInstanceUncachedWith (translateFuelFix (translateStep tenv) fuel) mn y.1 y.2
        ⟨o, .bitVector k⟩) (instEN mn lvls dom rest) hint top named) ctx s
      mctx mref cctx cref wm (w, t) w1 := by
    unfold Tools.ShippingChildInv.armCont at hrA
    rw [houts] at hrA
    exact hrA
  rcases controlCached_runsW L hwm hdm hr' with hit | ⟨sm, wa, wb, hwa, hda, lowerRun, recordRun⟩
  · have hlk := cacheLookupValidated_returns hit
    rw [hlk.1]
    exact ⟨hok, TGrows.refl _, hok.recs _ _ (hlk.2 _ rfl)⟩
  · obtain ⟨d', conns, sA, wc, wd, hwc, hdc', hwb, hdb, subD, hArgs, hdes1, hdes2, hdes3,
      hcase⟩ := instUncached_namWE L hrecK hdc hnoclk hsp hlen hwa hda lowerRun
    obtain ⟨-, -, subR⟩ := keepsW L (fun L' => recordTranslation_keepsC L' D
      (instEN mn lvls dom rest) w (!named && !(instEN mn lvls dom rest).isFVar && !top))
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
      have hW : WidthIs sA w (τ (instEN mn lvls dom rest)) :=
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
          w (τ (instEN mn lvls dom rest)) := by
        rw [← hkτ]
        exact (hwW.mono gN).of_wires rfl
      rw [hsm]
      exact ⟨tI.record _ _ hWI, ((gSA.trans gW).trans gN).of_wires rfl, hWI.of_wires rfl⟩

end walkE

end Tools.ShippingGateParentRun

#print axioms Tools.ShippingGateParentRun.instUncached_namWE
#print axioms Tools.ShippingGateParentRun.desW_instE
#print axioms Tools.ShippingGateParentRun.namW_instE
#print axioms Tools.ShippingGateParentRun.typW_instE
