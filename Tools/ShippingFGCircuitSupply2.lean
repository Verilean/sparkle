import Tools.ShippingFGCircuitSupply
import Tools.ShippingFGCircuitArtifact
set_option autoImplicit false
-- FG circuit pilot S1d, unit 1: what of `StaticEnv` / `MachineDefinesAt` / `hE` the existing theorems supply. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # S1d-1: supplying the environment facts of the four roots

* `StaticEnv` (S1c) quantifies over EVERY world. Under the cell premise `SetGet cref` (inside `CellPrem` = C.EN-4) that is refutable (`not_staticEnv`): a `set` of the Core state
  with another environment is a world where `envAt` differs. So `StaticEnv` must NOT be supplied and the `_static` theorems of S1c are conditional on something that C.EN-4 makes
  false (they stay as proved implications; they are not used as the way to supply `hd`/`hE` any more).
* `hd` (`MachineDefines`) IS supplied, by the existing row `h_A_P06` (the inner hypothesis of `FGLedgerPremisesStmtG`, `∀ c, TgtRun P X c → … → MachineDefines mctx' mref cctx' cref c q.d.shape`),
  at the root `c = X` (`TgtRun.top`), with the context from `Start` (A.P-02) and the package from `genGP`: `machineDefines_of_hA6`.
  The only link is `p.d.shape = X.machineData.shape` (from `EndpointLink.data`, i.e. `hl`).
* `hE` (`RootInEnv (envAt cref w)`): the part the RUN gives is existence (`run_reads_const`: the `getConstInfo X` the run performed returned `ci` which is in `envAt cref w1`).
  Moving it to the start environment `envAt cref w` needs the run-local snapshot `EnvSnapshot cref w1 w` (the existing open statement; run-local, NOT `∀ w`).
  The CONTENT (the entry is the quoted definition) is the named fact `QuoteFact` (FG rows: C.EN-4 / ENV cache). `rootInEnv_of_quote` combines them. -/
namespace Tools.ShippingFGCircuitSupply2
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG Tools.ShippingGen2
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt EnvSnapshot)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingStRefCorrespondence (SetGet setW)
open Tools.ShippingChildInv (readOf)

/-! ## `StaticEnv` is refuted by `SetGet cref` -/

theorem not_staticEnv {cref : ST.Ref IO.RealWorld Core.State} {E : Environment} (hsg : SetGet cref) (w : Void IO.RealWorld) :
    ¬ StaticEnv cref E := by
  intro hs
  let s := readOf cref w
  let e1 : Environment := s.env.setMainModule `a
  let e2 : Environment := s.env.setMainModule `b
  have h1 := hs (setW cref { s with env := e1 } w)
  have h2 := hs (setW cref { s with env := e2 } w)
  unfold envAt at h1 h2
  rw [hsg] at h1 h2
  have h12 : e1 = e2 := h1.trans h2.symm
  have h3 : e1.mainModule = e2.mainModule := congrArg Environment.mainModule h12
  have ha : e1.mainModule = `a := rfl
  have hb : e2.mainModule = `b := rfl
  rw [ha, hb] at h3
  exact absurd h3 (by decide)

/-! ## `hd` from `h_A_P06` -/

theorem machineDefines_of_hA6 {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context}
    {P : Pkgs ι dom} {X : Name} {p : Pkg ι dom} {d : Tools.ShippingMachineAuto.MachineData}
    (hstart : AdmCtx L.O.quiet mctx cctx)
    (hA6 : ∀ c, TgtRun P X c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' →
        MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hP : P X = some p) (hdata : p.d = d) : MachineDefines mctx mref cctx cref X d.shape := by
  have := hA6 X TgtRun.top p hP mctx cctx hstart
  rw [hdata] at this
  exact this

/-- `hd` from the witness (`Start`) and the link: the form the four roots use -/
theorem machineDefines_of_witness {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State}
    {cref : ST.Ref IO.RealWorld Core.State} {L : Laws mref cref} {mctx : Meta.Context} {cctx : Core.Context}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} {parameters : List (String × Nat)}
    {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    {P : Pkgs ι dom} {X : Name} {p : Pkg ι dom} {d : Tools.ShippingMachineAuto.MachineData} {k : Nat}
    {obs : (i : ι) → (Nat → Signal (dom i) Bool) → ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    (hw : EntryWitness ReflectsAll L X parameters mctx cctx w w' b D)
    (hA6 : ∀ c, TgtRun P X c → ∀ q : Pkg ι dom, P c = some q →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' →
        MachineDefines mctx' mref cctx' cref c q.d.shape)
    (hP : P X = some p) (hl : EndpointLink d k obs p) : MachineDefines mctx mref cctx cref X d.shape :=
  machineDefines_of_hA6 hw.1.1 hA6 hP hl.data

/-! ## `hE`: the run gives existence, the snapshot moves it to the start, the quote fact gives content -/

/-- the run's own `getConstInfo X` read returns a constant of the environment of the world where it ran, and under the run-local snapshot of that world and the start
the same constant is in the start environment. (`w1` is the run's read world, tied by the `getConstInfo` run; not a `∀`.) -/
theorem run_reads_const {X : Name} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w') :
    ∃ (w1 w2 : Void IO.RealWorld) (ci : ConstantInfo),
      RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 ∧ (envAt cref w1).find? X = some ci ∧
        (EnvSnapshot cref w1 w → (envAt cref w).find? X = some ci) := by
  obtain ⟨_, _, ci, w1, w2, _, _, _, _, hget, _, _⟩ := Tools.ShippingEntrySoundness.synthesizeCombinationalCore_reads hr
  refine ⟨w1, w2, ci, hget, Tools.ShippingEntryReadsLinked.getConstInfo_value hget, fun snap => ?_⟩
  have h : envAt cref w = envAt cref w1 := snap
  rw [h]
  exact Tools.ShippingEntryReadsLinked.getConstInfo_value hget

/-- the content fact (NOT supplied; FG rows C.EN-4 / ENV cache): whatever the environment holds under `X` is the quoted definition -/
def QuoteFact (env : Environment) (X : Name) (ty val : Lean.Expr) : Prop :=
  ∀ ci : ConstantInfo, env.find? X = some ci → ∃ d : DefinitionVal, ci = .defnInfo d ∧ d.levelParams = [] ∧ d.type = ty ∧ d.value = val

theorem rootInEnv_of_quote {env : Environment} {X : Name} {ty val : Lean.Expr} {ci : ConstantInfo}
    (hq : QuoteFact env X ty val) (hf : env.find? X = some ci) : ∃ d : DefinitionVal, RootInEnv env X ty val d := by
  obtain ⟨d, rfl, hl, ht, hv⟩ := hq ci hf
  exact ⟨d, hf, hl, ht, hv⟩

/-- `hE` for any root: existence from the run, content from `QuoteFact`, the single run-local link `EnvSnapshot cref w1 w` -/
theorem hE_of_run {X : Name} {ty val : Lean.Expr} {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld} {M : Sparkle.IR.AST.Module} {D : Sparkle.IR.AST.Design}
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinationalCore X [] false) mctx mref cctx cref w (M, D) w')
    (hq : QuoteFact (envAt cref w) X ty val) :
    ∃ (w1 w2 : Void IO.RealWorld) (ci : ConstantInfo), RunsTo (getConstInfo X) mctx mref cctx cref w1 ci w2 ∧
      (EnvSnapshot cref w1 w → ∃ d : DefinitionVal, RootInEnv (envAt cref w) X ty val d) := by
  obtain ⟨w1, w2, ci, hget, -, hsnap⟩ := run_reads_const hr
  exact ⟨w1, w2, ci, hget, fun snap => rootInEnv_of_quote hq (hsnap snap)⟩

end Tools.ShippingFGCircuitSupply2

#print axioms Tools.ShippingFGCircuitSupply2.not_staticEnv
#print axioms Tools.ShippingFGCircuitSupply2.machineDefines_of_hA6
#print axioms Tools.ShippingFGCircuitSupply2.machineDefines_of_witness
#print axioms Tools.ShippingFGCircuitSupply2.hE_of_run
