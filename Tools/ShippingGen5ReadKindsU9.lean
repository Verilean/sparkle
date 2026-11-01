import Tools.Prototype.DGenProv
import Tools.Prototype.DGenStored2
import Tools.ShippingGen5ReadKindsU7
import Tools.ShippingGen5Env
import Tools.ShippingGen5RunReads
set_option autoImplicit false
-- Built: kjob lake build Tests.Gen5.ReadKindsU9Check exit 0 (822 jobs) as rk14v-730dbea5 on 730dbea50ab741ce759f1fef02bbe80f84634f78, approved at 730dbea5 (conditional intermediate, M5/FG not complete). Freeze: scripts/gen5/DG_READKINDS_U9_FREEZE.md. No sorry / axiom / native_decide.

/-! # DG-READKINDS U9 (freeze scripts/gen5/DG_READKINDS_U9_FREEZE.md)

U9c `readMachine_agrees_runReads_at` (CONDITIONAL on the named-world `ReadsAt` premises h0/h1/hR and `declName = X`),
U9a `dataE_run` (a successful `dataE r` run exposes the three reflected pieces),
U9b `storedFromRead_of_dataE_run` (CONDITIONAL on `hag` and the denotation antecedent; `hb`/`hl` replaced by the successful run).
Not claimed: `hag`, `hK`, `hall`/DG-ENV C0, existence of the runs, `envR = envR'`, `ci ∈ envR`, `GateDefines`, `srcDom`, `ls`/`outs`/`nexts`, hq, coverage, FG.
`hR` is a conditional premise over all matching (w1,w2,w3) triples, not a completed supply of the finite five worlds. -/
namespace Tools.ShippingGen5ReadKindsU9
open Lean Meta
open Sparkle.Compiler.Elab
open Tools.ShippingEntrySoundness
open Tools.ShippingMachineCommand Tools.ShippingMachineEntry
open Tools.Prototype.DGenProv
open Tools.ShippingGen5ReadKinds Tools.ShippingGen5ReadKindsU5
open Tools.ShippingChildInv
open Tools.ShippingMachineAuto (MachineData)

theorem readMachine_agrees_runReads_at {declName X : Lean.Name} {allowGate : Bool}
    {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
    {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
    {w : Void IO.RealWorld} {r : Read} {w' : Void IO.RealWorld}
    (hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w')
    {ws ws' w5 w6 : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design} {b : Bool}
    {ci : Lean.ConstantInfo} {envR envR' : Lean.Environment} {shape : MachineShape}
    (R : Tools.ShippingGen5RunReads.RunReadsAt mctx mref cctx cref X ws ws' raw D b ci envR envR' shape w5 w6)
    {env₀ : Lean.Environment}
    (h0 : Tools.ShippingGen5Env.ReadsAt env₀ cref w)
    (h1 : ∀ (env : Lean.Environment) (v1 : Void IO.RealWorld),
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w env v1 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref v1)
    (hR : ∀ w1 w2 w3 : Void IO.RealWorld,
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w5 →
      Tools.ShippingGen5Env.ReadsAt env₀ cref w1 ∧ Tools.ShippingGen5Env.ReadsAt env₀ cref w2 ∧
        Tools.ShippingGen5Env.ReadsAt env₀ cref w3)
    (hX : declName = X) :
    r.entry = entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR) ∧
      r.shape = shape := by
  subst hX
  obtain ⟨_, w1, w2, w3, _, _, _, _, hget, henv, henv', _⟩ := R.chain
  have hshape := R.shapeEq
  obtain ⟨hA1, hA2, hA3⟩ := hR w1 w2 w3 hget henv henv'
  obtain ⟨ci', env, v1, v2, he, hc, hent, hsh⟩ := Tools.Prototype.DGenProv.readMachine_run hrun
  have hci' : env₀.find? declName = some ci' := Tools.ShippingGen5Env.ci_of_readsAt hc (h1 env v1 he)
  have hci : env₀.find? declName = some ci := Tools.ShippingGen5Env.ci_of_readsAt hget hA1
  have hcc : ci' = ci := Option.some.inj (hci'.symm.trans hci)
  obtain ⟨_, p1, p2, p3⟩ := Tools.ShippingGen5Env.envR_of_readsAt he h0
  obtain ⟨_, q1, q2, q3⟩ := Tools.ShippingGen5Env.envR_of_readsAt henv hA2
  obtain ⟨_, s1, s2, s3⟩ := Tools.ShippingGen5Env.envR_of_readsAt henv' hA3
  subst hcc
  have hent' : r.entry = entryConst true false [] ci' (instancePredicate env) (userInliner env) (structEnv env) := hent
  have hsh' : machineShape? false [] (entryConst true false [] ci' (instancePredicate env) (userInliner env)
      (structEnv env)) (structEnv env) = some r.shape := hsh
  clear hent hsh
  rw [p1, p2, p3] at hent' hsh'
  rw [q1, q2, q3] at hshape
  rw [s3] at hshape
  rw [q1, q2, q3]
  refine ⟨hent', ?_⟩
  exact Option.some.inj (hsh'.symm.trans hshape)

theorem dataE_run {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (h : RunsTo (dataE r) mctx mref cctx cref w e w') :
    ∃ body dom lay : Lean.Expr,
      reflExpr r.shape.body = .ok body ∧ reflExpr r.dom = .ok dom ∧
      layoutE r.shape.layout = some lay ∧ e = dataPure r body dom lay := by
  rcases hb : reflExpr r.shape.body with msg | body
  · exfalso
    simp only [dataE, hb] at h
    obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  rcases hd : reflExpr r.dom with msg | dom
  · exfalso
    simp only [dataE, hb, hd] at h
    obtain ⟨_, _, _, h⟩ := RunsTo.bind h
    obtain ⟨_, _, h1, _⟩ := RunsTo.bind h
    exact (throwError_not_runs _ h1).elim
  rcases hl : layoutE r.shape.layout with _ | lay
  · exfalso
    simp only [dataE, hb, hd, hl] at h
    exact (throwError_not_runs _ h).elim
  simp only [dataE, hb, hd, hl] at h
  exact ⟨_, _, _, rfl, rfl, rfl, (RunsTo.pure_eq h)⟩

theorem storedFromRead_of_dataE_run (hag : Tools.Prototype.DGenStored2.ReflExprAgree)
    {r : Read} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {w : Void IO.RealWorld} {e : Lean.Expr} {w' : Void IO.RealWorld}
    (hrun : RunsTo (dataE r) mctx mref cctx cref w e w') (d : MachineData) :
    ∃ body lay : Lean.Expr, reflExpr r.shape.body = .ok body ∧ layoutE r.shape.layout = some lay ∧
      (Tools.Prototype.DGenStored2.ShapeDenotes (dataShapeE r.shape body lay) d.shape →
        Tools.Prototype.DGenProv.StoredFromRead d r) := by
  obtain ⟨body, _, lay, hb, _, hl, _⟩ := dataE_run hrun
  exact ⟨body, lay, hb, hl, fun hK =>
    Tools.Prototype.DGenStored2.storedFromRead_of_kernelRead hag d r body lay hb hl hK⟩

end Tools.ShippingGen5ReadKindsU9
