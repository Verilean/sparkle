import Tools.ShippingFGCircuitS2dKids
set_option autoImplicit false
-- FG circuit pilot S2g: `HftKidsGates` reduced to the closed declarations of the two callees + finitely many environment queries. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law. Results: docs/FG-CIRCUIT-PILOT.md §33.

open Lean Elab Command Meta in
/-- `quote_decl% c as T V Vi Ti`: closed `Lean.Expr` quotes of the declaration's type `T` and value `V`, and of `userInliner env` of the value (`Vi`) and of the type (`Ti`) in the build's environment (the last two are SNAPSHOTS; the facts that they are what the environment's inliner returns are named hypotheses, `ui_val`/`ui_ty`) -/
elab "quote_decl% " c:ident " as " t:ident v:ident vi:ident ti:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  liftTermElabM do
    let ci ← getConstInfo declName
    let env ← getEnv
    let add (n : Ident) (e : Lean.Expr) : MetaM Unit :=
      let v := Tools.ShippingFGCircuitRoots.exprToE e
      addAndCompile (.defnDecl { name := n.getId, levelParams := [], type := mkConst ``Lean.Expr, value := v, hints := .abbrev, safety := .safe })
    add t ci.type
    add v ci.value!
    add vi (Sparkle.Compiler.Elab.userInliner env ci.value!)
    add ti (Sparkle.Compiler.Elab.userInliner env ci.type)

quote_decl% Sparkle.IP.Net.HTTP.httpGetByte as Tools.ShippingFGCircuitS2gGates.httpType Tools.ShippingFGCircuitS2gGates.httpValue Tools.ShippingFGCircuitS2gGates.httpInlValue Tools.ShippingFGCircuitS2gGates.httpInlType
quote_decl% Sparkle.IP.Bus.PCIe.tlpCplByte as Tools.ShippingFGCircuitS2gGates.tlpType Tools.ShippingFGCircuitS2gGates.tlpValue Tools.ShippingFGCircuitS2gGates.tlpInlValue Tools.ShippingFGCircuitS2gGates.tlpInlType

namespace Tools.ShippingFGCircuitS2gGates
open Lean Sparkle.Compiler.Elab Tools.ShippingFGCircuitS1lReader Tools.ShippingFGCircuitS2dKids

/-- the body of a gate-peeled value (the term the instance predicate is applied to first) -/
def peeled (e : Lean.Expr) : Lean.Expr :=
  match mixedGatePeel e with
  | some p => p.2
  | none => e

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

def GatesOn (d : DefinitionVal) (ip : Lean.Expr → Bool) : Prop :=
  (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true

/-- the two refusal facts on the closed declaration with type `T` and value `V` (kernel-evaluated; the instance predicate is asked at the peeled body only) -/
theorem http_gates_V (d : DefinitionVal) (hty : d.type = httpType) (hval : d.value = httpValue)
    (ip : Lean.Expr → Bool) (hip : ip (peeled httpValue) = false) : GatesOn d ip := by
  obtain ⟨bs, hmp⟩ : ∃ bs, mixedGatePeel httpValue = some (bs, peeled httpValue) := ⟨_, by with_unfolding_all rfl⟩
  unfold GatesOn certifiedShape? mixedCertifiedShape?
  simp only [hval, hty, hmp]
  constructor
  · with_unfolding_all rfl
  · unfold unifiedInstanceRoot hierInstRoot
    simp only [hip, Bool.false_and, Bool.false_or]
    with_unfolding_all rfl

/-- the two refusal facts on the closed declaration with type `T` and the INLINED value `Vi` (kernel-evaluated; the instance predicate is asked at the peeled body only) -/
theorem http_gates_Vi (d : DefinitionVal) (hty : d.type = httpType) (hval : d.value = httpInlValue)
    (ip : Lean.Expr → Bool) (hip : ip (peeled httpInlValue) = false) : GatesOn d ip := by
  obtain ⟨bs, hmp⟩ : ∃ bs, mixedGatePeel httpInlValue = some (bs, peeled httpInlValue) := ⟨_, by with_unfolding_all rfl⟩
  unfold GatesOn certifiedShape? mixedCertifiedShape?
  simp only [hval, hty, hmp]
  constructor
  · with_unfolding_all rfl
  · unfold unifiedInstanceRoot hierInstRoot
    simp only [hip, Bool.false_and, Bool.false_or]
    with_unfolding_all rfl

/-- the two refusal facts on the closed declaration with type `T` and value `V` (kernel-evaluated; the instance predicate is asked at the peeled body only) -/
theorem tlp_gates_V (d : DefinitionVal) (hty : d.type = tlpType) (hval : d.value = tlpValue)
    (ip : Lean.Expr → Bool) (hip : ip (peeled tlpValue) = false) : GatesOn d ip := by
  obtain ⟨bs, hmp⟩ : ∃ bs, mixedGatePeel tlpValue = some (bs, peeled tlpValue) := ⟨_, by with_unfolding_all rfl⟩
  unfold GatesOn certifiedShape? mixedCertifiedShape?
  simp only [hval, hty, hmp]
  constructor
  · with_unfolding_all rfl
  · unfold unifiedInstanceRoot hierInstRoot
    simp only [hip, Bool.false_and, Bool.false_or]
    with_unfolding_all rfl

/-- the two refusal facts on the closed declaration with type `T` and the INLINED value `Vi` (kernel-evaluated; the instance predicate is asked at the peeled body only) -/
theorem tlp_gates_Vi (d : DefinitionVal) (hty : d.type = tlpType) (hval : d.value = tlpInlValue)
    (ip : Lean.Expr → Bool) (hip : ip (peeled tlpInlValue) = false) : GatesOn d ip := by
  obtain ⟨bs, hmp⟩ : ∃ bs, mixedGatePeel tlpInlValue = some (bs, peeled tlpInlValue) := ⟨_, by with_unfolding_all rfl⟩
  unfold GatesOn certifiedShape? mixedCertifiedShape?
  simp only [hval, hty, hmp]
  constructor
  · with_unfolding_all rfl
  · unfold unifiedInstanceRoot hierInstRoot
    simp only [hip, Bool.false_and, Bool.false_or]
    with_unfolding_all rfl

open Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitFinal4 Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1kStmt

/-- the facts about the environment `env` that `EntryGates env X` asks, for a callee `X` of closed type `T` and value `V`: (root) the declaration is the closed one; (ui) the inliner sends the value to `Vi` and fixes the type; (ip) the instance predicate is false at the peeled body of `V` and of `Vi` — the finitely many queries, each at ONE closed term or ONE name; no snapshot of the world, no statement about other environments -/
structure KidGateFacts (env : Environment) (X : Name) (T V Vi : Lean.Expr) : Prop where
  root : ∃ d : DefinitionVal, RootInEnv env X T V d
  ui_val : userInliner env V = Vi
  ui_ty : userInliner env T = T
  ip_val : instancePredicate env (peeled V) = false
  ip_inl : instancePredicate env (peeled Vi) = false

/-- `EntryGates` from the gates on the declaration and on its inlined form (whichever `entryConst` returns) -/
theorem entryGates_of_two {env : Environment} {X : Name} {T V Vi : Lean.Expr} {d : DefinitionVal}
    (h : RootInEnv env X T V d) (hv : userInliner env V = Vi) (ht : userInliner env T = T)
    (g1 : GatesOn d (instancePredicate env)) (g2 : GatesOn { d with value := Vi, type := T } (instancePredicate env)) :
    EntryGates env X := by
  intro E hE
  rw [entry₀_of_rootInEnv h] at hE
  cases Option.some.inj hE
  obtain ⟨-, -, hty, hval⟩ := id h
  have hi : inlinedConst (userInliner env) (.defnInfo d) = .defnInfo { d with value := Vi, type := T } := by
    simp only [inlinedConst, hval, hv, hty, ht]
  have G1 : certifiedShape? false [] (.defnInfo d) = none ∧ mixedCertifiedShape? false [] (.defnInfo d) (instancePredicate env) = none := by
    exact ⟨Option.isNone_iff_eq_none.mp g1.1, Option.isNone_iff_eq_none.mp g1.2⟩
  have G2 : certifiedShape? false [] (.defnInfo { d with value := Vi, type := T }) = none ∧
      mixedCertifiedShape? false [] (.defnInfo { d with value := Vi, type := T }) (instancePredicate env) = none := by
    exact ⟨Option.isNone_iff_eq_none.mp g2.1, Option.isNone_iff_eq_none.mp g2.2⟩
  unfold entryConst
  rw [hi]
  split <;> (try split) <;> first | exact G1 | exact G2

theorem httpGate_of_facts {env : Environment} (hf : KidGateFacts env hftHttp httpType httpValue httpInlValue) : EntryGates env hftHttp := by
  obtain ⟨⟨d, h⟩, hv, ht, ip1, ip2⟩ := hf
  obtain ⟨-, -, hty, hval⟩ := id h
  exact entryGates_of_two h hv ht (http_gates_V d hty hval _ ip1) (http_gates_Vi _ rfl rfl _ ip2)

theorem tlpGate_of_facts {env : Environment} (hf : KidGateFacts env hftTlp tlpType tlpValue tlpInlValue) : EntryGates env hftTlp := by
  obtain ⟨⟨d, h⟩, hv, ht, ip1, ip2⟩ := hf
  obtain ⟨-, -, hty, hval⟩ := id h
  exact entryGates_of_two h hv ht (tlp_gates_V d hty hval _ ip1) (tlp_gates_Vi _ rfl rfl _ ip2)

/-- the gate facts of BOTH callees (NAMED HYPOTHESIS, FG D.T-4g, now finite: closed declarations + inliner/instance-predicate queries at named points) -/
def HftKidsGateFacts (e : Environment) : Prop :=
  KidGateFacts e hftHttp httpType httpValue httpInlValue ∧ KidGateFacts e hftTlp tlpType tlpValue tlpInlValue

theorem hftKidsGates_of_facts {e : Environment} (h : HftKidsGateFacts e) : HftKidsGates e :=
  ⟨httpGate_of_facts h.1, tlpGate_of_facts h.2⟩

/-! ## the final statement with `hkgates` replaced -/
section Final

open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitS1iEnv
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingFGCircuitS1kRoot Tools.ShippingFGCircuitS1kStmt Tools.ShippingFGCircuitS1kPkg
open Tools.ShippingFGCircuitS1qEndpoint
open Tools.ShippingFGCircuitS1mCD Tools.ShippingFGCircuitS1pCD Tools.ShippingFGCircuitS1rCD
open Tools.ShippingFGCircuitS1tFinal Tools.ShippingFGCircuitS1uSrc Tools.ShippingFGCircuitS1xNoRaw
open Tools.ShippingFGCircuitRunLocal Tools.ShippingFGCircuitS1zClose Tools.ShippingFGCircuitS2aClose
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5EnvFrame3 (CellPrem)

/-- `HftFinalStmtOffLNKK` (S2d) with `hkgates : HftKidsGates (envAt cref w)` replaced by `hkgfacts : HftKidsGateFacts (envAt cref w)` (14 explicit hypotheses; the last is the only one that changed) -/
def HftFinalStmtOffLNKKG (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ (hlink : HftRootLink) {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem Tools.ShippingChildFresh.MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp Sparkle.IP.Net.HTTP.httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp Sparkle.IP.Bus.PCIe.tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p : Pkg ι (fun _ => defaultDomain), GPt (ι := ι) lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hkenv : HftKidsStartEnv L.O (envAt cref w))
    (hkgfacts : HftKidsGateFacts (envAt cref w)),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMonoV CV (envAt cref w) (GPt (ι := ι) lvl (envAt cref w))
        (PostRunOff mctx mref cctx cref w hftRoot D') hftRoot shHft mm b D' p

theorem synth_hftPcieOutByte_finalOffLNKKG (CV : CDRel) (Ob : Environment → Prop) (hOb : ∀ env, Ob env → HftObOf CV env) :
    HftFinalStmtOffLNKKG Ob CV := by
  intro hlink ι mref cref L lvl env₀ mctx cctx w w' b D' hstart hr hcell hchk hRdH hRdT hCD hTop hkenv hkgfacts
  exact synth_hftPcieOutByte_finalOffLNKK CV Ob hOb hlink L lvl env₀ hstart hr hcell hchk hRdH hRdT hCD hTop hkenv
    (hftKidsGates_of_facts hkgfacts)

theorem synth_hftPcieOutByte_finalOffLNKKG_Z : HftFinalStmtOffLNKKG HftObCDZ cdvZ := synth_hftPcieOutByte_finalOffLNKKG cdvZ _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffLNKKG_Y : HftFinalStmtOffLNKKG HftObCDY cdvY := synth_hftPcieOutByte_finalOffLNKKG cdvY _ (fun _ h => h)
theorem synth_hftPcieOutByte_finalOffLNKKG_X : HftFinalStmtOffLNKKG HftObCDX cdvX := synth_hftPcieOutByte_finalOffLNKKG cdvX _ (fun _ h => h)

end Final

end Tools.ShippingFGCircuitS2gGates

#print axioms Tools.ShippingFGCircuitS2gGates.http_gates_V
#print axioms Tools.ShippingFGCircuitS2gGates.tlp_gates_Vi
#print axioms Tools.ShippingFGCircuitS2gGates.entryGates_of_two
#print axioms Tools.ShippingFGCircuitS2gGates.hftKidsGates_of_facts
#print axioms Tools.ShippingFGCircuitS2gGates.synth_hftPcieOutByte_finalOffLNKKG_Z
