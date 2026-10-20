import Tools.ShippingInstArmGrow
import Tools.ShippingInstanceEntrySoundness

variable {tenv : Lean.Environment}

/-! # The S6 n-ary shape tail over `armCont` (worker N, round 1)

WRITTEN, NOT BUILT.

`Tools.ShippingInstanceEntrySoundness.synthesizeMixedCertified_instanceN_sound`
proves the n-ary instance shape of a parent with the child PINNED by the
global premise `SubSynthDefines mn mc dc`: it enters once, as `rw [hsub sub
hSubM] at tr`, after which the proof reads only `tr : Returns (the arm's
continuation on (mc, dc)) …`. That continuation is `armCont rec mn (mc, dc)`
(`Tools/ShippingInstArmGrow.lean`). Here the tail of that proof is re-stated
over `armCont rec mn y` for ANY pair `y` — the pair the run's own child
synthesis returned — with no pinned-child premise:

* `InstanceNShape` — the conclusion of `InstanceNPreserves` with the child
  pair `y` in the place of `(mc, dc)` (the child's port shape stays an
  antecedent: it is a fact about the child's own compile);
* `armCont_instanceN_tail` — from `Returns (armCont … y (instEN mn lvls dF
  (argIds.map .fvar)) "out" false true)` in the prepared context and state,
  the emitted output port and `assign`, and `finishSynth`'s pair: that shape.
  The proof is the text of the S6 monolith from the line after the rewrite
  (`ShippingInstanceEntrySoundness.lean` 1500–1697), `mc := y.1`, `dc := y.2`;
  the domain argument `dF` is any expression (a binder or a closed constant:
  the arm does not read it, the arity guard drops it). -/
namespace Tools.ShippingGateParentRun

open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder
open Tools.ShippingTranslateSoundness (Returns recordTranslation_returns
  emitAssign_body_cons)
open Tools.ShippingEntrySoundness (MReturns RunsTo emitLeaves_single
  addOutput_state addClockReset_facts)
open Tools.ShippingMemoryEntrySoundness (mixedGateBVar?_pos)
open Tools.ShippingMixedSourceBridge (inputExpr)
open Sparkle.IR.Semantics (Env)
open Tools.ShippingMixedEntrySoundness (Setup start prepare Admissible
  prepare_returns prepare_layout synthesizeMixedCertified_returns)
open Tools.ShippingMixedInputSoundness (empty_layout)
open Tools.ShippingMixedInvariant (translateStep_fvar_returns)
open Tools.ShippingRegisterSoundness (not_allocated_out prepare_const
  admissible_zero prepare_wires_allocated init_wires)
open Tools.ShippingBoolSourceSoundness (translateControlCachedWith_returns)
open Tools.ShippingTranslateSoundness (cacheLookupValidated_returns)
open Tools.ShippingInstanceEntrySoundness
open Tools.ShippingChildInv (armCont)

/-- **The n-ary instance shape of a parent pair `(m, d)` over the child pair
`y`** — the conclusion of `InstanceNPreserves` (for the fresh ids `ids` and
the translation cache `cache` of the run) with `y` in the place of the
pinned `(mc, dc)`: if the child's design has no further module, its inputs
are `ports` (no clock / reset), its one output is `out`, one port per
argument, then the parent body is one instance of `y.1` over the
port-ordered connections plus the output alias, the design holds exactly
`y.1`, and each connection reads the prepared input wire of its argument. -/
def InstanceNShape (declName : Name) (bs : List (Name × MixedGateBinder)) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (argIds : List FVarId)
    (y : Sparkle.IR.AST.Module × Design) (m : Sparkle.IR.AST.Module) (d : Design) : Prop :=
  ∀ (wOut : Nat) (ports : List Port),
    y.2.modules = [] →
    y.1.inputs = ports →
    y.1.outputs = [⟨"out", .bitVector wOut⟩] →
    (∀ p ∈ ports, (p.name == "clk") = false ∧ (p.name == "rst") = false) →
    ports.length = argIds.length →
    ∃ (instName outW : String) (conns : List (String × Sparkle.IR.AST.Expr)),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (ws : Nat → Nat) (vals : (i : Nat) → BitVec (ws i)),
    let a := start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName)
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ i (h : i < argIds.length), p.bits (argIds[i]'h) = some ⟨ws i, vals i⟩) →
    m.body = [.inst y.1.name instName (conns.reverse ++ [("out", .ref outW)]),
      .assign "out" (.ref outW)] ∧
    d.modules = [y.1] ∧
    outW ≠ "out" ∧
    ∃ aWs : List String, aWs.length = argIds.length ∧
      conns.reverse = ((ports.zip (argIds.map Lean.Expr.fvar)).zip aWs).map
        (fun pw => (pw.1.1.name, Sparkle.IR.AST.Expr.ref pw.2)) ∧
      ∀ i (h : i < aWs.length),
        env0 (aWs[i]'h) = (vals i).toNat ∧ aWs[i]'h ≠ "out"

set_option maxHeartbeats 2000000 in
/-- **The S6 shape tail over `armCont`**: the run's own child pair `y`, no
pinned-child premise. -/
theorem armCont_instanceN_tail {declName : Name} {bs : List (Name × MixedGateBinder)}
    {ids : List FVarId} {cache : IO.Ref (ExprStructMap String)}
    {mn : Name} {lvls : List Level} {dF : Lean.Expr} {argIds : List FVarId}
    {y : Sparkle.IR.AST.Module × Design}
    {w : String} {sm0 st : CircuitState} {ty : Sparkle.IR.Type.HWType}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (tr : Returns (armCont (translateFuelFix (translateStep tenv) 1048575) mn y
        (instEN mn lvls dF (argIds.map Lean.Expr.fvar)) "out" false true)
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))).context
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))).state
      w sm0)
    (ht : st = (CircuitM.emitAssign "out" (.ref w) (CircuitM.addOutput "out" ty sm0).2).2)
    (hm : m = (addClockResetIfSequential st.module).finalize) (hd : d = st.design) :
    InstanceNShape declName bs ids cache argIds y m d := by
  intro wOut ports hdc hins houts hnoclk hlenP
  unfold armCont at tr
  rw [houts] at tr
  simp only [] at tr
  have empty0 := empty_layout (entryCompilerState false cache)
    (Sparkle.IR.ModuleName.ofDecl declName) (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName))).state.translateRecord = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec w rfl
    rw [record0] at dead
    simp at dead
  rw [instanceUncached_run] at missRun
  obtain ⟨cs0, sG, hget0, k1⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) missRun
  obtain ⟨hcs0, hsG⟩ := Returns.get hget0
  subst hcs0 hsG
  have hpdes : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName))).state.design =
      Design.empty (Sparkle.IR.ModuleName.ofDecl declName) :=
    prepare_design (bs.zip ids) _
  rw [hdc] at k1
  obtain ⟨u0, sA, hAdd0, k2⟩ := Returns.bind (m := instAddModules _ []) k1
  obtain ⟨-, hsA⟩ := Returns.pure (by exact hAdd0 : Returns (pure ()) _ _ u0 sA)
  subst hsA
  obtain ⟨uR, sB, hReg, k3⟩ := Returns.bind (m := instRegisterChild _ y.1) k2
  have hsB := instRegisterChild_fresh (by rw [hpdes]; rfl) (by rw [hpdes]; rfl) hReg
  obtain ⟨conns0, sC, hClk, k4⟩ := Returns.bind (m := instClkRst [] y.1.inputs) k3
  rw [hins] at hClk
  obtain ⟨hconns0, hsC⟩ := instClkRst_skip hnoclk hClk
  subst hconns0 hsC
  have hfil : y.1.inputs.filter (fun p => p.name != "clk" && p.name != "rst") = ports := by
    rw [hins]
    apply List.filter_eq_self.mpr
    intro p hp
    obtain ⟨h1, h2⟩ := hnoclk p hp
    simp [bne, h1, h2]
  rw [hfil, instEN_spineArgs] at k4
  -- the arity guard: one more spine argument (the domain) than ports
  obtain ⟨uG, sH, hGuard, k5⟩ := Returns.bind (m := instArityCheck mn _ _) k4
  unfold instArityCheck at hGuard
  rw [if_neg (by simp [hlenP])] at hGuard
  obtain ⟨-, hsH⟩ := Returns.pure hGuard
  subst hsH
  -- the argument walk stays opaque until the valuation is known
  have hdrop : (dF :: argIds.map Lean.Expr.fvar).drop
      ((dF :: argIds.map Lean.Expr.fvar).length - ports.length) =
      argIds.map Lean.Expr.fvar := by
    simp [hlenP]
  rw [hdrop] at k5
  obtain ⟨conns, sF, hArgs, k6⟩ := Returns.bind (m := instArgs _ _ _ 0) k5
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  subst hcsP hsP2
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  obtain ⟨hCacheM, hsQ⟩ := Returns.liftMetaM_mreturns hCacheRead
  subst hsQ
  rw [record0, instHit_empty] at k8
  simp only [] at k8
  obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire "out" _ true) k8
  obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
  obtain ⟨uP, sV, hPut, k10⟩ :=
    Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
  have hsV := Returns.liftMetaM hPut
  subst hsV
  obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
  obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
  obtain ⟨uL, sL, hLink, k11⟩ := Returns.bind (m := instLinkCheck _ _ _) k11
  obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
  rw [hsL] at k11
  obtain ⟨uE, sI, hEmit, k12⟩ :=
    Returns.bind (m := CompilerM.emitInstance y.1.name _ _) k11
  have hsI := emitInstanceC_returns hEmit
  obtain ⟨hwEq, hsmR⟩ := Returns.pure k12
  subst hwEq
  have hrec := recordTranslation_returns record
  refine ⟨instName, w, conns, ?_⟩
  intro bools bits env0 ws vals a p adm hb
  have empty := empty_layout (entryCompilerState false cache)
    (Sparkle.IR.ModuleName.ofDecl declName) env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) (Sparkle.IR.ModuleName.ofDecl declName))
    empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [ps] at hsB
  rw [pc] at hArgs
  have fuelEq : translateFuelFix (translateStep tenv) 1048575 =
      translateStepWith (translateFallback tenv)
        (translateFuelFix (translateStep tenv) 1048574) := rfl
  rw [fuelEq] at hArgs
  have designSB : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).sourceBindings = s.sourceBindings :=
    fun _ _ => rfl
  have designMod : ∀ (s : CircuitState) dd,
      ({ s with design := dd } : CircuitState).module = s.module :=
    fun _ _ => rfl
  -- one prepared input wire per argument
  obtain ⟨aWs, hlenW, hQ⟩ := list_choice argIds.length
    (fun i hi wv =>
      Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache)
            (Sparkle.IR.ModuleName.ofDecl declName))).context
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache)
            (Sparkle.IR.ModuleName.ofDecl declName))).state.sourceBindings
        (argIds[i]'hi) = some wv ∧
      ({ name := wv, ty := .bitVector (ws i) } : Port) ∈
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache)
            (Sparkle.IR.ModuleName.ofDecl declName))).state.module.wires ∧
      env0 wv = (vals i).toNat)
    (fun i hi => prepared.1.bits (argIds[i]'hi) (ws i) (vals i) (hb i hi))
  have hpairsLen : (ports.zip (argIds.map Lean.Expr.fvar)).length = aWs.length := by
    simp [hlenP, hlenW]
  obtain ⟨hsQ', hconnsEq⟩ := instArgs_resolve
    (ports.zip (argIds.map Lean.Expr.fvar)) aWs [] 0 conns sQ hpairsLen
    (fun k hk hk' => by
      have hkA : k < argIds.length := by rw [← hlenW]; exact hk'
      refine ⟨argIds[k]'hkA, ?_, ?_⟩
      · simp
      · rw [hsB, designSB]
        exact (hQ k hkA hk').1)
    hArgs
  have hbodyR : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName))).state.module.body = [] := by
    rw [prepared.2.2.1]; rfl
  have hpdesR : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName))).state.design =
      Design.empty (Sparkle.IR.ModuleName.ofDecl declName) := prepare_design (bs.zip ids) _
  have inputNotOut : ∀ (q : Sparkle.IR.AST.Port),
      q ∈ (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache)
          (Sparkle.IR.ModuleName.ofDecl declName))).state.module.wires →
      q.name ≠ "out" := by
    intro q hq eq
    have alloc := prepare_wires_allocated bools bits (bs.zip ids) _
      (by rw [show (start (entryCompilerState false cache)
            (Sparkle.IR.ModuleName.ofDecl declName)).state =
          CircuitM.init (Sparkle.IR.ModuleName.ofDecl declName) from rfl, init_wires]
          intro x hx; cases hx) q hq
    rw [eq] at alloc
    exact not_allocated_out alloc
  have addOutBody : ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).body = mo.body :=
    fun _ _ => rfl
  have stBody : st.module.body =
      .assign "out" (.ref w) ::
        .inst y.1.name instName
          ((((⟨"out", .bitVector wOut⟩ : Port).name, Sparkle.IR.AST.Expr.ref w) ::
            conns).reverse) ::
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache)
              (Sparkle.IR.ModuleName.ofDecl declName))).state.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state]
    show _ :: (sm0.module.addOutput _).body = _
    rw [addOutBody, hrec]
    show _ :: smR.module.body = _
    rw [hsmR, hsI]
    show _ :: (_ :: sN.module.body) = _
    rw [hsN, (CircuitM.freshName_spec _ _ _).2.2, hsW]
    rw [(CircuitM.makeWire_spec "out" _ true _).2.2.1]
    rw [hsQ', hsB, designMod]
  have mBody : m.body = (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName))).state.module.body.reverse ++
      [.inst y.1.name instName
        ((((⟨"out", .bitVector wOut⟩ : Port).name, Sparkle.IR.AST.Expr.ref w) ::
          conns).reverse),
       .assign "out" (.ref w)] := by
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).body = _
    simp only [Sparkle.IR.AST.Module.finalize,
      (addClockReset_facts st.module).1, stBody]
    simp
  have stDesign : st.design = ((prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache)
        (Sparkle.IR.ModuleName.ofDecl declName))).state.design).addModule y.1 := by
    rw [ht]
    show sm0.design = _
    rw [hrec]
    show smR.design = _
    rw [hsmR, hsI]
    show sN.design = _
    rw [hsN]
    rw [show ∀ s, ((CircuitM.freshName (toString "inst_" ++ toString y.1.name) false s).2).design
        = s.design from fun s => freshName_design _ _ s, hsW]
    rw [makeWire_design]
    rw [hsQ', hsB]
  have wNotOut : w ≠ "out" := by
    intro eq
    have alloc := CircuitM.makeWire_allocated "out"
      (Sparkle.IR.Type.HWType.bitVector wOut) true sQ
    rw [← houtW, eq] at alloc
    exact not_allocated_out alloc
  refine ⟨?_, ?_, wNotOut, aWs, hlenW, ?_, ?_⟩
  · rw [mBody, hbodyR]
    simp
  · rw [hd, stDesign, hpdesR]
    rfl
  · rw [hconnsEq]
    simp
  · intro i hi
    have hiA : i < argIds.length := by rw [← hlenW]; exact hi
    obtain ⟨-, hdecl, hval⟩ := hQ i hiA hi
    exact ⟨hval, inputNotOut _ hdecl⟩

end Tools.ShippingGateParentRun
