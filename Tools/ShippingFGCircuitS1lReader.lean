import Tools.ShippingFGCircuitS1iRoots
set_option autoImplicit false
-- FG circuit pilot S1l: CheckedStart's gates/reader for counterLoop connected to facts about a FINITE input. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1l: `CheckedEnv.gates` / `CheckedEnv.reader` of `counterLoop` from a closed declaration and a few named facts

`CheckedEnv.gates` (`entryGatesB env₀ X = true`) and `CheckedEnv.reader` (`ReaderAt lvl env₀ X dd`) were evaluation statements about `env₀`.  Here they are reduced to statements about
* the closed declaration `d` (`RootInEnv`: `d.type`/`d.value` are the closed kernel terms), and
* the three environment-derived arguments of the entry constant: `instancePredicate env₀`, `userInliner env₀`, `structEnv env₀`.

**General (any root).** `GatesOnDecl`, `ReaderOnDecl` (the two statements with the three arguments explicit) and `checkedEnv_of_decl`.

**counterLoop.** What the kernel evaluates here (proved, standard axioms only): `certifiedShape?` / `mixedCertifiedShape?` on the closed declaration (the gates), `mixedGatePeel`, `srcDomOf` (given the `Expr.find?` fact), `machDom?`, `machOuts?`, `dataOfCore` with `lvl` fuel 1000000 — down to the whole `counterLoop.machineData` structure (`counterLoop_dataOfAt`).
The remaining facts are named, each about ONE closed term or ONE name:
* `CounterLoopExtern` (env independent): `packTupleInputs` and `rootFloat` (`partial`, calling externs) fix `counterLoopValue`; `Expr.find?` (an `opaque` extern) finds no `runCircuitH` application in it.  Rows: DG-DATAOF T-X, DG-COVER S-COV-FLOAT.
* `CounterLoopEnvFacts env₀`: the root is the closed declaration `d` and `machineShape?` (a `partial` machine reader; not kernel-evaluable) reads `d` as the data's shape (DG-COVER, C.RK-6, C.CV-4); `userInliner env₀` fixes the value and the type; `instancePredicate env₀` is false on the value; `(structEnv env₀).proj` is `none` at `Signal.loop` (DG-ENV: these are what the three derived arguments are *queried* at; found by running the readers with logging arguments in `MetaM`, Check10 SNAPSHOT10).
`ReadsAt env₀ cref w` (DG-ENV C0) and the run facts are unchanged.  This does not supply the facts, and bundling them into one structure is not counted as a reduction. -/
namespace Tools.ShippingFGCircuitS1lReader
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitRoots4
open Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1iHead
open Tools.ShippingGen5DataOf
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingStRefCorrespondence (ReadWorld)

/-! ## general: a closed declaration and the three derived arguments -/

/-- the entry constant of a closed declaration `d` with the three environment-derived arguments explicit -/
def EntryOfDecl (d : DefinitionVal) (ip : Lean.Expr → Bool) (ui : Lean.Expr → Lean.Expr) (se : StructEnv) : ConstantInfo :=
  entryConst true false [] (.defnInfo d) ip ui se

/-- the two refusal facts of the gate, on a closed declaration and the instance predicate -/
def GatesOnDecl (d : DefinitionVal) (ip : Lean.Expr → Bool) (ui : Lean.Expr → Lean.Expr) (se : StructEnv) : Prop :=
  (certifiedShape? false [] (EntryOfDecl d ip ui se)).isNone = true ∧
  (mixedCertifiedShape? false [] (EntryOfDecl d ip ui se) ip).isNone = true

/-- the reader's outputs (the shape and the data) on a closed declaration and the three derived arguments -/
def ReaderOnDecl (lvl : Lean.Expr → Nat) (d : DefinitionVal) (ip : Lean.Expr → Bool) (ui : Lean.Expr → Lean.Expr) (se : StructEnv)
    (dd : Tools.ShippingMachineAuto.MachineData) : Prop :=
  machineShape? false [] (EntryOfDecl d ip ui se) se = some dd.shape ∧
  dataOfAt lvl (EntryOfDecl d ip ui se) se dd.shape = some dd

theorem entryGatesB_of_gatesOnDecl {env : Environment} {X : Name} {ty val : Lean.Expr} {d : DefinitionVal}
    (h : RootInEnv env X ty val d) (hg : GatesOnDecl d (instancePredicate env) (userInliner env) (structEnv env)) :
    entryGatesB env X = true := by
  rw [entryGatesB_of_rootInEnv h]
  obtain ⟨h1, h2⟩ := hg
  unfold EntryOfDecl at h1 h2
  simp [h1, h2]

theorem readerAt_of_readerOnDecl {lvl : Lean.Expr → Nat} {env : Environment} {X : Name} {ty val : Lean.Expr} {d : DefinitionVal}
    {dd : Tools.ShippingMachineAuto.MachineData}
    (h : RootInEnv env X ty val d) (hr : ReaderOnDecl lvl d (instancePredicate env) (userInliner env) (structEnv env) dd) :
    ReaderAt lvl env X dd := by
  intro E hE
  rw [entry₀_of_rootInEnv h] at hE
  cases Option.some.inj hE
  exact hr

/-- `CheckedEnv` from a closed declaration and the three derived arguments -/
theorem checkedEnv_of_decl {lvl : Lean.Expr → Nat} {env₀ : Environment} {X : Name} {ty val : Lean.Expr} {d : DefinitionVal}
    {dd : Tools.ShippingMachineAuto.MachineData}
    (h : RootInEnv env₀ X ty val d)
    (hg : GatesOnDecl d (instancePredicate env₀) (userInliner env₀) (structEnv env₀))
    (hr : ReaderOnDecl lvl d (instancePredicate env₀) (userInliner env₀) (structEnv env₀) dd) :
    CheckedEnv lvl env₀ X ty val dd :=
  ⟨⟨d, h⟩, entryGatesB_of_gatesOnDecl h hg, readerAt_of_readerOnDecl h hr⟩

/-- if the inliner fixes the declaration's value and type, the entry constant is the declaration (no `machineShape?` evaluation is needed) -/
theorem entryOfDecl_eq {d : DefinitionVal} {ip : Lean.Expr → Bool} {ui : Lean.Expr → Lean.Expr} {se : StructEnv}
    (h1 : ui d.value = d.value) (h2 : ui d.type = d.type) : EntryOfDecl d ip ui se = .defnInfo d := by
  have hi : inlinedConst ui (.defnInfo d) = .defnInfo d := by
    simp only [inlinedConst, h1, h2]
  unfold EntryOfDecl entryConst
  split <;> simp [hi]

/-! ## counterLoop: what the kernel evaluates -/

/-- the closed facts about the `partial`/extern helpers on `counterLoopValue` (env independent; NOT proved: the helpers are opaque to the kernel) -/
structure CounterLoopExtern : Prop where
  pack : Sparkle.Compiler.MachTupleIn.packTupleInputs counterLoopValue = counterLoopValue
  rootFloat : Sparkle.Compiler.MachRawSurface.rootFloat counterLoopValue = counterLoopValue
  find : counterLoopValue.find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8) = none

/-- the facts about the environment `env₀` that the entry/reader evaluation queries (each at ONE closed term or ONE name) -/
structure CounterLoopEnvFacts (env₀ : Environment) : Prop where
  root : ∃ d : DefinitionVal, RootInEnv env₀ ``counterLoop counterLoopType counterLoopValue d ∧
    machineShape? false [] (.defnInfo d) (structEnv env₀) = some counterLoop.machineData.shape
  ui_val : userInliner env₀ counterLoopValue = counterLoopValue
  ui_ty : userInliner env₀ counterLoopType = counterLoopType
  ip_val : instancePredicate env₀ counterLoopValue = false
  proj_loop : (structEnv env₀).proj ``Sparkle.Core.Signal.Signal.loop = none

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

theorem machRoot_counterLoop (f : Name → Option (Name × Nat × Nat)) (hf : f ``Sparkle.Core.Signal.Signal.loop = none) :
    machRoot f counterLoopValue [] = ([], none, none, counterLoopValue) := by
  obtain ⟨args, hs⟩ : ∃ args, inlSpine counterLoopValue [] = (Lean.Expr.const ``Sparkle.Core.Signal.Signal.loop [], args) :=
    ⟨_, by with_unfolding_all rfl⟩
  have hm : machRunApp? counterLoopValue = none := by with_unfolding_all rfl
  obtain ⟨a, b, hab⟩ : ∃ a b, counterLoopValue = Lean.Expr.app a b := ⟨_, _, by with_unfolding_all rfl⟩
  unfold machRoot
  split
  · rename_i heq; rw [hab] at heq; cases heq
  · simp [hm, hs, hf]

theorem srcDomOf_counterLoop (se : StructEnv) (hf : se.proj ``Sparkle.Core.Signal.Signal.loop = none)
    (hfind : counterLoopValue.find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8) = none) :
    srcDomOf se counterLoopType counterLoopValue = some (eDom, 0) := by
  unfold srcDomOf
  rw [machRoot_counterLoop se.proj hf]
  simp only [hfind]
  with_unfolding_all rfl

theorem dataOfCore_counterLoop (lvl : Lean.Expr → Nat) (hlvl : lvl counterLoop.machineData.shape.body = 1000000) :
    dataOfCore lvl counterLoop.machineData.shape 0 eDom = some counterLoop.machineData := by
  unfold dataOfCore
  rw [hlvl]
  with_unfolding_all rfl

/-- the reader's data for `counterLoop`: the kernel evaluates everything but the `partial`/extern helpers and the queried name (`Signal.loop` in `proj`) -/
theorem counterLoop_dataOfAt (lvl : Lean.Expr → Nat) (hlvl : lvl counterLoop.machineData.shape.body = 1000000)
    (d : DefinitionVal) (hty : d.type = counterLoopType) (hval : d.value = counterLoopValue)
    (se : StructEnv) (hproj : se.proj ``Sparkle.Core.Signal.Signal.loop = none) (hx : CounterLoopExtern) :
    dataOfAt lvl (.defnInfo d) se counterLoop.machineData.shape = some counterLoop.machineData := by
  have hmp : mixedGatePeel counterLoopValue = some ([], counterLoopValue) := by with_unfolding_all rfl
  have hsd := srcDomOf_counterLoop se hproj hx.find
  have hfront : dataOfFront (.defnInfo d) se counterLoop.machineData.shape counterLoopValue Sparkle.Compiler.MachRawSurface.rootFloat = some (0, eDom) := by
    unfold dataOfFront
    have hT : (ConstantInfo.defnInfo d).toConstantVal.type = counterLoopType := hty
    have hT2 : (ConstantInfo.defnInfo d).type = counterLoopType := hty
    simp only [hmp, Option.bind_some, hx.rootFloat, hT2, hsd]
    with_unfolding_all rfl
  unfold dataOfAt
  simp only [ConstantInfo.value?, hval, hx.pack]
  unfold dataOfFrom
  rw [hfront]
  simp only [Option.bind_some]
  exact dataOfCore_counterLoop lvl hlvl

/-- the gates on the closed declaration: `certifiedShape?` is evaluated by the kernel, `mixedCertifiedShape?` queries the instance predicate at the value only -/
theorem counterLoop_gates (d : DefinitionVal) (hty : d.type = counterLoopType) (hval : d.value = counterLoopValue)
    (ip : Lean.Expr → Bool) (hip : ip counterLoopValue = false) :
    (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true := by
  constructor
  · unfold certifiedShape?
    simp only [hval]
    with_unfolding_all rfl
  · have hmp : mixedGatePeel counterLoopValue = some ([], counterLoopValue) := by with_unfolding_all rfl
    unfold mixedCertifiedShape?
    simp only [hval, hty, hmp]
    unfold unifiedInstanceRoot hierInstRoot
    simp only [hip, Bool.false_and, Bool.false_or]
    with_unfolding_all rfl

theorem counterLoop_gatesOnDecl (d : DefinitionVal) (hty : d.type = counterLoopType) (hval : d.value = counterLoopValue)
    (ip : Lean.Expr → Bool) (ui : Lean.Expr → Lean.Expr) (se : StructEnv) (hip : ip counterLoopValue = false)
    (hu1 : ui counterLoopValue = counterLoopValue) (hu2 : ui counterLoopType = counterLoopType) :
    GatesOnDecl d ip ui se := by
  have he : EntryOfDecl d ip ui se = .defnInfo d := entryOfDecl_eq (by rw [hval]; exact hu1) (by rw [hty]; exact hu2)
  unfold GatesOnDecl
  rw [he]
  exact counterLoop_gates d hty hval ip hip

theorem counterLoop_readerOnDecl (lvl : Lean.Expr → Nat) (hlvl : lvl counterLoop.machineData.shape.body = 1000000)
    (d : DefinitionVal) (hty : d.type = counterLoopType) (hval : d.value = counterLoopValue)
    (ip : Lean.Expr → Bool) (ui : Lean.Expr → Lean.Expr) (se : StructEnv)
    (hu1 : ui counterLoopValue = counterLoopValue) (hu2 : ui counterLoopType = counterLoopType)
    (hshape : machineShape? false [] (.defnInfo d) se = some counterLoop.machineData.shape)
    (hproj : se.proj ``Sparkle.Core.Signal.Signal.loop = none) (hx : CounterLoopExtern) :
    ReaderOnDecl lvl d ip ui se counterLoop.machineData := by
  have he : EntryOfDecl d ip ui se = .defnInfo d := entryOfDecl_eq (by rw [hval]; exact hu1) (by rw [hty]; exact hu2)
  unfold ReaderOnDecl
  rw [he]
  exact ⟨hshape, counterLoop_dataOfAt lvl hlvl d hty hval se hproj hx⟩

/-- **`CheckedEnv` for `counterLoop` from the named finite facts** (`CounterLoopEnvFacts env₀`, `CounterLoopExtern`, the fuel) -/
theorem counterLoop_checkedEnv_of_finite (lvl : Lean.Expr → Nat) (env₀ : Environment)
    (hlvl : lvl counterLoop.machineData.shape.body = 1000000) (hx : CounterLoopExtern) (hf : CounterLoopEnvFacts env₀) :
    CheckedEnv lvl env₀ ``counterLoop counterLoopType counterLoopValue counterLoop.machineData := by
  obtain ⟨d, hroot, hshape⟩ := hf.root
  obtain ⟨-, -, hty, hval⟩ := id hroot
  exact checkedEnv_of_decl hroot
    (counterLoop_gatesOnDecl d hty hval _ _ _ hf.ip_val hf.ui_val hf.ui_ty)
    (counterLoop_readerOnDecl lvl hlvl d hty hval _ _ _ hf.ui_val hf.ui_ty hshape hf.proj_loop hx)

/-- **`counterLoop_final11`**: `counterLoop_final10` with `hchk : CheckedStart` replaced by the finite facts and the link `ReadsAt env₀ cref w` -/
theorem counterLoop_final11 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterLoop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAt ``counterLoop mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hlvl : lvl counterLoop.machineData.shape.body = 1000000) (hx : CounterLoopExtern) (hf : CounterLoopEnvFacts env₀)
    (hlink : ReadsAt env₀ cref w) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterLoop D' b raw) ∧
    ∃ (mm : MonoTy shCounter) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterLoop D') ``counterLoop shCounter mm b D' p :=
  Tools.ShippingFGCircuitS1iRoots.counterLoop_final10 L lvl env₀ hstart hr hhead hcell
    ⟨counterLoop_checkedEnv_of_finite lvl env₀ hlvl hx hf, hlink⟩

end Tools.ShippingFGCircuitS1lReader

#print axioms Tools.ShippingFGCircuitS1lReader.counterLoop_dataOfAt
#print axioms Tools.ShippingFGCircuitS1lReader.counterLoop_gates
#print axioms Tools.ShippingFGCircuitS1lReader.counterLoop_checkedEnv_of_finite
#print axioms Tools.ShippingFGCircuitS1lReader.counterLoop_final11
