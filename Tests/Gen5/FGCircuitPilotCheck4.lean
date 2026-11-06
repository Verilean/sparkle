import Tools.ShippingFGCircuitFinal
set_option autoImplicit false
-- FG circuit pilot S1e check. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED. Results: docs/FG-CIRCUIT-PILOT.md §10.

/-! # FGCircuitPilotCheck4

1. SIGNATURES: the expected types of `counterLoop_hsrc`, `designTransport_of_leaf`, `counterLoop_final2`, written here independently and compared with the actual types by `isDefEq`; single-point MUTANTS must be rejected.
2. HYPS: the explicit hypotheses of `counterLoop_final2` are read from its type: exactly `L lvl hw hr hA6 hRead hE`. `hsrc` and `htr` (and every supplied premise) must NOT be among them, and no hypothesis type may mention `sorryAx`.
3. AXIOMS of every new name.
4. SNAPSHOT4: the observation `monoObs` of `counterLoop` is not vacuous (the first cycles of the loop, by kernel evaluation). -/
namespace Tests.Gen5.FGCircuitPilotCheck4
open Lean Meta Elab Command Term Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingMachineEntry (MachineDefines MachineCloses)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Compiler.Elab Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises

abbrev W := Void IO.RealWorld

/-! ## 1. expected statements -/

def ExpHsrc : Prop :=
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    RootReader lvl env ``counterLoop counterLoop.machineData →
    ∃ p : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env ``counterLoop = some p ∧
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shCounter counterLoop bools bits
def MutHsrcOtherObs : Prop :=   -- the observation of another declaration
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    RootReader lvl env ``counterLoop counterLoop.machineData →
    ∃ p : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env ``counterLoop = some p ∧
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shShift4 shift4Loop bools bits
def MutHsrcOtherRoot : Prop :=  -- the package of another root
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    RootReader lvl env ``counterLoop counterLoop.machineData →
    ∃ p : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env ``shift4Loop = some p ∧
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shCounter counterLoop bools bits
def MutHsrcNoReader : Prop :=   -- without the reader premise
  ∀ {ι : Type} (lvl : Lean.Expr → Nat) (env : Environment),
    ∃ p : Pkg ι (fun _ => defaultDomain),
      genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) env ``counterLoop = some p ∧
      ∀ (i : ι) bools bits, p.src i bools bits = monoObs shCounter counterLoop bools bits

def ExpTransport : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {d : MachineData} {mctx : Meta.Context} {cctx : Core.Context} {w w1 : W} {raw b : Sparkle.IR.AST.Module} {D₀ D' : Sparkle.IR.AST.Design},
    p.d = d → LeafFacts d → Start L mctx cctx w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D₀) w1 →
    MachineDefines mctx mref cctx cref p.decl p.d.shape → MachineCloses mctx mref cctx cref p.decl p.d.shape →
    Tools.ShippingGen5DCEntry.PostT1 b raw →
    DesignTransport p p.decl b raw D₀ D'
def MutTransportNoRun : Prop :=   -- without the core run
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {d : MachineData} {mctx : Meta.Context} {cctx : Core.Context} {w : W} {raw b : Sparkle.IR.AST.Module} {D₀ D' : Sparkle.IR.AST.Design},
    p.d = d → LeafFacts d → Start L mctx cctx w →
    MachineDefines mctx mref cctx cref p.decl p.d.shape → MachineCloses mctx mref cctx cref p.decl p.d.shape →
    Tools.ShippingGen5DCEntry.PostT1 b raw →
    DesignTransport p p.decl b raw D₀ D'
def MutTransportNoLeaf : Prop :=  -- without the leaf facts
  ∀ {ι : Type} {dom : ι → DomainConfig} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State} (L : Laws mref cref) (p : Pkg ι dom)
    {d : MachineData} {mctx : Meta.Context} {cctx : Core.Context} {w w1 : W} {raw b : Sparkle.IR.AST.Module} {D₀ D' : Sparkle.IR.AST.Design},
    p.d = d → Start L mctx cctx w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D₀) w1 →
    MachineDefines mctx mref cctx cref p.decl p.d.shape → MachineCloses mctx mref cctx cref p.decl p.d.shape →
    Tools.ShippingGen5DCEntry.PostT1 b raw →
    DesignTransport p p.decl b raw D₀ D'

def ExpFinal2 : Prop :=
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    EntryWitness ReflectsAll L ``counterLoop [] mctx cctx w w' b D' →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ c, TgtRun (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w)) ``counterLoop c →
      ∀ q : Pkg ι (fun _ => defaultDomain),
        genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape) →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def MutFinal2NoRun : Prop :=      -- compile success dropped
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    EntryWitness ReflectsAll L ``counterLoop [] mctx cctx w w' b D' →
    (∀ c, TgtRun (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w)) ``counterLoop c →
      ∀ q : Pkg ι (fun _ => defaultDomain),
        genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape) →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def MutFinal2NoExists : Prop :=   -- the post-processing existence dropped from the conclusion
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    EntryWitness ReflectsAll L ``counterLoop [] mctx cctx w w' b D' →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ c, TgtRun (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w)) ``counterLoop c →
      ∀ q : Pkg ι (fun _ => defaultDomain),
        genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape) →
    RootReader lvl (envAt cref w) ``counterLoop counterLoop.machineData →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p
def MutFinal2NoReader : Prop :=   -- the reader premise dropped (a stronger, unsupported statement)
  ∀ {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    {ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop} (L : Laws mref cref) (lvl : Lean.Expr → Nat)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : W} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design} {d : DefinitionVal},
    EntryWitness ReflectsAll L ``counterLoop [] mctx cctx w w' b D' →
    RunsTo (synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w' →
    (∀ c, TgtRun (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w)) ``counterLoop c →
      ∀ q : Pkg ι (fun _ => defaultDomain),
        genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w) c = some q →
        ∀ (mctx' : Meta.Context) (cctx' : Core.Context), AdmCtx L.O.quiet mctx' cctx' → MachineDefines mctx' mref cctx' cref c q.d.shape) →
    RootInEnv (envAt cref w) ``counterLoop counterLoopType counterLoopValue d →
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p

def whitelist : List Name := [``ExpHsrc, ``MutHsrcOtherObs, ``MutHsrcOtherRoot, ``MutHsrcNoReader, ``ExpTransport, ``MutTransportNoRun, ``MutTransportNoLeaf,
  ``ExpFinal2, ``MutFinal2NoRun, ``MutFinal2NoExists, ``MutFinal2NoReader]

def norm (e : Lean.Expr) : MetaM Lean.Expr :=
  Meta.transform e (post := fun e => do
    if let .const c _ := e.getAppFn then
      if whitelist.contains c then
        if let some e' ← unfoldDefinition? e then return .visit e'.headBeta
    return .done e)

set_option maxHeartbeats 4000000 in
run_cmd liftTermElabM do
  let same (thm exp : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    unless ci.levelParams.isEmpty do throwError "{thm}: level parameters"
    let a ← norm ci.type
    let e ← norm (mkConst exp)
    unless ← withReducible (isDefEq a e) do throwError "{thm}: type is NOT the expected statement {exp}"
  let differs (thm mu0 : Name) : MetaM Unit := do
    let ci ← getConstInfo thm
    let a ← norm ci.type
    let e ← norm (mkConst mu0)
    if ← withReducible (isDefEq a e) then throwError "{thm}: the MUTANT {mu0} was accepted"
  let S := `Tools.ShippingFGCircuitSrc
  let T := `Tools.ShippingFGCircuitTransport
  let F := `Tools.ShippingFGCircuitFinal
  same (S ++ `counterLoop_hsrc) ``ExpHsrc
  same (T ++ `designTransport_of_leaf) ``ExpTransport
  same (F ++ `counterLoop_final2) ``ExpFinal2
  let mut nm : Nat := 0
  for (t, mu) in [(S ++ `counterLoop_hsrc, ``MutHsrcOtherObs), (S ++ `counterLoop_hsrc, ``MutHsrcOtherRoot), (S ++ `counterLoop_hsrc, ``MutHsrcNoReader),
      (T ++ `designTransport_of_leaf, ``MutTransportNoRun), (T ++ `designTransport_of_leaf, ``MutTransportNoLeaf),
      (F ++ `counterLoop_final2, ``MutFinal2NoRun), (F ++ `counterLoop_final2, ``MutFinal2NoExists), (F ++ `counterLoop_final2, ``MutFinal2NoReader)] do
    differs t mu; nm := nm + 1
  logInfo m!"FGCIRCUIT4 SIGNATURES: counterLoop_hsrc, designTransport_of_leaf, counterLoop_final2 equal their independently written expected types; {nm} mutants rejected"

/-! ## 2. the hypotheses that remain, by name (read from the theorem type) -/

def explicitBinders (thm : Name) : MetaM (List (String × Lean.Expr)) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut hs : List (String × Lean.Expr) := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.binderInfo.isExplicit then hs := hs ++ [(d.userName.toString, d.type)]
    return hs

run_cmd liftTermElabM do
  let F := `Tools.ShippingFGCircuitFinal
  let thm := F ++ `counterLoop_final2
  let bs ← explicitBinders thm
  let names := bs.map (·.1)
  let expected := ["L", "lvl", "hw", "hr", "hA6", "hRead", "hE"]
  unless names == expected do throwError "{thm}: hypotheses are {names}, expected {expected}"
  for supplied in ["hsrc", "htr", "hd", "hc", "hcl", "hP", "hl", "hTop", "hpost"] do
    if names.contains supplied then throwError "{thm}: {supplied} is still a hypothesis"
  for (n, t) in bs do
    if t.getUsedConstants.contains ``sorryAx then throwError "{thm}: hypothesis {n} mentions sorryAx"
  -- no hypothesis is `DesignTransport` or the `src` agreement itself
  for (n, t) in bs do
    if t.getUsedConstants.contains ``Tools.ShippingFGCircuitBridge.DesignTransport then throwError "{thm}: hypothesis {n} is DesignTransport"
    if t.getUsedConstants.contains ``Tools.ShippingFGCircuit.monoObs then throwError "{thm}: hypothesis {n} states the observation (hsrc)"
  -- the statement mentions its own root only
  let ci ← getConstInfo thm
  let consts := ci.type.getUsedConstants
  for o in [``Sparkle.Tests.SignalLoopTest.shift4Loop, ``Sparkle.Tests.SignalLoopTest.counterEnableLoop, ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal] do
    if consts.contains o then throwError "{thm}: mentions another root {o}"
  logInfo m!"FGCIRCUIT4 HYPS counterLoop_final2: {String.intercalate " " names}"
  logInfo "FGCIRCUIT4 HYPS: hsrc (D.D-3) and DesignTransport (D.T-4) are NOT hypotheses; hr/hw (antecedent), hA6, hRead (RootReader), hE remain"

/-! ## 3. axioms of every new name -/
run_cmd liftTermElabM do
  let S := `Tools.ShippingFGCircuitSrc
  let T := `Tools.ShippingFGCircuitTransport
  let F := `Tools.ShippingFGCircuitFinal
  let names : List Name := [S ++ `list_ext_of_map_eval, S ++ `counterLoop_loop_zero, S ++ `counterLoop_loop_succ, S ++ `counterLoop_src_eq, S ++ `genGP_root_src,
    S ++ `genGP_root_canon_src, S ++ `counterLoop_hsrc, T ++ `topShips_design_irrel, T ++ `leaf_instFree_of_run, T ++ `designTransport_of_leaf,
    F ++ `hTop_of_leaf2, F ++ `counterLoop_final2]
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
  logInfo m!"FGCIRCUIT4 AXIOMS: {names.length} names, standard axioms only (no sorryAx, no native_decide)"

/-! ## 4. SNAPSHOT4: the observation is not vacuous -/

/-- the first cycles of `counterLoop` (through the recurrence proved in `Src`): 0 at cycle 0, 3 at cycle 3 -/
theorem counterLoop_first_cycles : counterLoop.val 0 = 0#8 ∧ counterLoop.val 3 = 3#8 := by
  have z := Tools.ShippingFGCircuitSrc.counterLoop_loop_zero (fun _ => Signal.pure false) (fun _ _ => Signal.pure 0)
  have s := Tools.ShippingFGCircuitSrc.counterLoop_loop_succ (fun _ => Signal.pure false) (fun _ _ => Signal.pure 0)
  refine ⟨z, ?_⟩
  show (Signal.loop (counterLoop.machineBody () (fun _ => Signal.pure false) (fun _ _ => Signal.pure 0))).val 3 = 3#8
  rw [s 2, s 1, s 0, z]
  decide

run_cmd logInfo "FGCIRCUIT4 SNAPSHOT4: the kernel proves counterLoop.val 0 = 0 and counterLoop.val 3 = 3, so `monoObs shCounter counterLoop` (the observation `hsrc` equates `p.src` with) is a non-trivial stream"

end Tests.Gen5.FGCircuitPilotCheck4
