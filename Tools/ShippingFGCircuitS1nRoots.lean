import Tools.ShippingFGCircuitS1lReader
set_option autoImplicit false
-- FG circuit pilot S1n: the S1l lift (`counterLoop_final11`) for the other three leaf roots. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED, no new law.

/-! # S1n: `X_final11` for shift4Loop, counterEnableLoop, arbiterSignal

Same shape as `counterLoop_final11` (S1l): the gates and the reader of the entry constant are reduced to the closed declaration, kernel-evaluated finite facts and named hypotheses.
Per root the named hypotheses are the instances of two common structures (`RootExtern`, `RootEnvFacts`, below); no field of the counterLoop structures is dropped:
* `RootExtern Vi`: `packTupleInputs`/`rootFloat` (`partial`, extern) fix the entry value / its peeled body, and `Expr.find?` (an `opaque` extern) finds no `runCircuitH` application in the peeled body.
* `RootEnvFacts env₀ X T V Vi dd name`: the root is the closed declaration `d`; `machineShape?` (a `partial` machine reader) reads the entry declaration (value `Vi`, type `T`) as `dd.shape`; `userInliner env₀` sends `V` to `Vi` and `T` to `T`; `instancePredicate env₀` is false on the peeled bodies of `V` and `Vi`; `(structEnv env₀).proj` is `none` at `name`.
What differs from counterLoop: the values of shift4Loop / counterEnableLoop / arbiterSignal are `fun`s over the gate binders, so the queried point of the instance predicate and the `rootFloat`/`find?` argument is the PEELED body (`mixedGatePeel`), not the value; `Signal.register` (shift4Loop) is the head that `machRoot` asks `proj` about; the arbiter's `userInliner` does change the value (the private state constants become literals), so its entry constant is the inlined declaration and the quote `arbiterInlinedValue` is a SNAPSHOT of `userInliner` of this build's environment (checked in Check12, named in `ui_val`). -/
open Lean Elab Command Meta in
elab "quote_inlined% " c:ident " as " n:ident : command => do
  let declName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo c
  liftTermElabM do
    let ci ← getConstInfo declName
    let v := Tools.ShippingFGCircuitRoots.exprToE (Sparkle.Compiler.Elab.userInliner (← getEnv) ci.value!)
    addAndCompile (.defnDecl { name := n.getId, levelParams := [], type := mkConst ``Lean.Expr, value := v, hints := .abbrev, safety := .safe })

quote_inlined% Sparkle.IP.Arbiter.RoundRobin.arbiterSignal as Tools.ShippingFGCircuitS1nRoots.arbiterInlinedValue

namespace Tools.ShippingFGCircuitS1nRoots
open Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5DeclConnect Tools.ShippingGen5FG
open Tools.ShippingFGCircuit Tools.ShippingFGCircuitRoots Tools.ShippingFGCircuitArtifact Tools.ShippingFGCircuitSupply2 Tools.ShippingFGCircuitCover Tools.ShippingFGCircuitBridge
open Tools.ShippingFGCircuitApply Tools.ShippingFGCircuitTransport Tools.ShippingFGCircuitSrc Tools.ShippingFGCircuitFinal Tools.ShippingFGCircuitLinked Tools.ShippingFGCircuitFinal4
open Sparkle.Tests.SignalLoopTest Tools.ShippingGenFGLedgerPremises Tools.ShippingFGCircuitRoots4
open Tools.ShippingFGCircuitS1hGates Tools.ShippingFGCircuitS1hQuote Tools.ShippingFGCircuitS1iEnv Tools.ShippingFGCircuitS1iHead
open Tools.ShippingFGCircuitS1lReader Tools.ShippingFGCircuitS1iRoots
open Tools.ShippingGen5DataOf
open Tools.ShippingEntrySoundness (RunsTo)
open Tools.ShippingEntryReadsLinked (envAt)
open Tools.ShippingGen5Env (ReadsAt)
open Tools.ShippingStRefCorrespondence (ReadWorld)
open Tools.ShippingMachineAuto (MachineData)

/-! ## common: the peeled body, the two named structures, the entry constant of an inlined declaration -/

/-- the body of a gate-peeled value (the term the instance predicate, `rootFloat` and `Expr.find?` are applied to) -/
def peeledBody (e : Lean.Expr) : Lean.Expr :=
  match mixedGatePeel e with
  | some p => p.2
  | none => e

/-- the closed facts about the `partial`/extern helpers on the entry value `Vi` (env independent; NOT proved: the helpers are opaque to the kernel) -/
structure RootExtern (Vi : Lean.Expr) : Prop where
  pack : Sparkle.Compiler.MachTupleIn.packTupleInputs Vi = Vi
  rootFloat : Sparkle.Compiler.MachRawSurface.rootFloat (peeledBody Vi) = peeledBody Vi
  find : (peeledBody Vi).find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8) = none

/-- the facts about `env₀` that the entry/reader evaluation queries (each at ONE closed term or ONE name); `V`/`T` the declaration's value/type, `Vi` the entry value (`userInliner` of `V`) -/
structure RootEnvFacts (env₀ : Environment) (X : Name) (T V Vi : Lean.Expr) (dd : MachineData) (projName : Name) : Prop where
  root : ∃ d : DefinitionVal, RootInEnv env₀ X T V d ∧
    machineShape? false [] (.defnInfo { d with value := Vi, type := T }) (structEnv env₀) = some dd.shape
  ui_val : userInliner env₀ V = Vi
  ui_ty : userInliner env₀ T = T
  ip_val : instancePredicate env₀ (peeledBody V) = false
  ip_inl : instancePredicate env₀ (peeledBody Vi) = false
  proj : (structEnv env₀).proj projName = none

/-- the entry constant of a closed declaration whose value the inliner rewrites to `V'` (type `T` fixed) -/
theorem entryOfDecl_inl {d : DefinitionVal} {ip : Lean.Expr → Bool} {ui : Lean.Expr → Lean.Expr} {se : StructEnv} {V' T : Lean.Expr}
    (hv : ui d.value = V') (ht : ui d.type = T)
    (g1 : (certifiedShape? false [] (.defnInfo d)).isNone = true)
    (g2 : (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true)
    (hs : (machineShape? false [] (.defnInfo { d with value := V', type := T }) se).isSome = true) :
    EntryOfDecl d ip ui se = .defnInfo { d with value := V', type := T } := by
  have hi : inlinedConst ui (.defnInfo d) = .defnInfo { d with value := V', type := T } := by
    simp only [inlinedConst, hv, ht]
  unfold EntryOfDecl entryConst
  simp [hi, g1, g2, hs]

/-- `CheckedEnv` for a root whose gates/data are given on the entry declaration `{d with value := V', type := T}` -/
theorem checkedEnv_of_inl {lvl : Lean.Expr → Nat} {env₀ : Environment} {X : Name} {T V V' : Lean.Expr} {d : DefinitionVal} {dd : MachineData}
    (h : RootInEnv env₀ X T V d)
    (hshape : machineShape? false [] (.defnInfo { d with value := V', type := T }) (structEnv env₀) = some dd.shape)
    (hv : userInliner env₀ V = V') (ht : userInliner env₀ T = T)
    (g1 : (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) (instancePredicate env₀)).isNone = true)
    (g2 : (certifiedShape? false [] (.defnInfo { d with value := V', type := T })).isNone = true ∧
      (mixedCertifiedShape? false [] (.defnInfo { d with value := V', type := T }) (instancePredicate env₀)).isNone = true)
    (hdata : dataOfAt lvl (.defnInfo { d with value := V', type := T }) (structEnv env₀) dd.shape = some dd) :
    CheckedEnv lvl env₀ X T V dd := by
  obtain ⟨-, -, hty, hval⟩ := id h
  have he : EntryOfDecl d (instancePredicate env₀) (userInliner env₀) (structEnv env₀) = .defnInfo { d with value := V', type := T } :=
    entryOfDecl_inl (by rw [hval]; exact hv) (by rw [hty]; exact ht) g1.1 g1.2 (by rw [hshape]; rfl)
  refine checkedEnv_of_decl h ?_ ?_
  · unfold GatesOnDecl; rw [he]; exact g2
  · unfold ReaderOnDecl; rw [he]; exact ⟨hshape, hdata⟩

/-- the data from the two evaluated pieces of the reader (`dataOfFront`, `dataOfCore`) -/
theorem dataOfAt_of_pieces {lvl : Lean.Expr → Nat} {d : DefinitionVal} {se : StructEnv} {dd : MachineData} {V' D : Lean.Expr} {nI : Nat}
    (hval : d.value = V') (hx : RootExtern V')
    (hfront : dataOfFront (.defnInfo d) se dd.shape V' Sparkle.Compiler.MachRawSurface.rootFloat = some (nI, D))
    (hcore : dataOfCore lvl dd.shape nI D = some dd) :
    dataOfAt lvl (.defnInfo d) se dd.shape = some dd := by
  unfold dataOfAt
  simp only [ConstantInfo.value?, hval, hx.pack]
  unfold dataOfFrom
  rw [hfront]
  exact hcore

/-- `machRoot` on a body that is an application, not a machine run, whose head `proj` does not know -/
theorem machRoot_of_head (f : Name → Option (Name × Nat × Nat)) {B : Lean.Expr} {N : Name} {ls : List Level} {args : List Lean.Expr}
    (hs : inlSpine B [] = (Lean.Expr.const N ls, args)) (hf : f N = none) (hm : machRunApp? B = none)
    (happ : ∃ a b, B = Lean.Expr.app a b) : machRoot f B [] = ([], none, none, B) := by
  obtain ⟨a, b, hab⟩ := happ
  unfold machRoot
  split
  · cases hab
  · simp [hm, hs, hf]

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

/-! ## shift4Loop -/

theorem shift4Loop_gates (d : DefinitionVal) (hty : d.type = shift4LoopType) (hval : d.value = shift4LoopValue)
    (ip : Lean.Expr → Bool) (hip : ip (peeledBody shift4LoopValue) = false) :
    (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true := by
  have hmp : mixedGatePeel shift4LoopValue = some ([(`input, MixedGateBinder.bits 8)], peeledBody shift4LoopValue) := by with_unfolding_all rfl
  constructor
  · unfold certifiedShape?
    simp only [hval]
    with_unfolding_all rfl
  · unfold mixedCertifiedShape?
    simp only [hval, hty, hmp]
    unfold unifiedInstanceRoot hierInstRoot
    simp only [hip, Bool.false_and, Bool.false_or]
    with_unfolding_all rfl

theorem shift4Loop_srcDomOf (se : StructEnv) (hf : se.proj ``Sparkle.Core.Signal.Signal.register = none)
    (hfind : (peeledBody shift4LoopValue).find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8) = none) :
    srcDomOf se shift4LoopType (peeledBody shift4LoopValue) = some (eDom, 0) := by
  obtain ⟨ls, args, hs⟩ : ∃ ls args, inlSpine (peeledBody shift4LoopValue) [] = (Lean.Expr.const ``Sparkle.Core.Signal.Signal.register ls, args) :=
    ⟨_, _, by with_unfolding_all rfl⟩
  have hm : machRunApp? (peeledBody shift4LoopValue) = none := by with_unfolding_all rfl
  have hroot := machRoot_of_head se.proj hs hf hm ⟨_, _, by with_unfolding_all rfl⟩
  unfold srcDomOf
  rw [hroot]
  simp only [hfind]
  with_unfolding_all rfl

theorem shift4Loop_dataOfCore (lvl : Lean.Expr → Nat) (hlvl : lvl shift4Loop.machineData.shape.body = 1000000) :
    dataOfCore lvl shift4Loop.machineData.shape 1 eDom = some shift4Loop.machineData := by
  unfold dataOfCore
  rw [hlvl]
  with_unfolding_all rfl

theorem shift4Loop_dataOfAt (lvl : Lean.Expr → Nat) (hlvl : lvl shift4Loop.machineData.shape.body = 1000000)
    (d : DefinitionVal) (hty : d.type = shift4LoopType) (hval : d.value = shift4LoopValue)
    (se : StructEnv) (hproj : se.proj ``Sparkle.Core.Signal.Signal.register = none) (hx : RootExtern shift4LoopValue) :
    dataOfAt lvl (.defnInfo d) se shift4Loop.machineData.shape = some shift4Loop.machineData := by
  have hmp : mixedGatePeel shift4LoopValue = some ([(`input, MixedGateBinder.bits 8)], peeledBody shift4LoopValue) := by with_unfolding_all rfl
  have hsd := shift4Loop_srcDomOf se hproj hx.find
  have hfront : dataOfFront (.defnInfo d) se shift4Loop.machineData.shape shift4LoopValue Sparkle.Compiler.MachRawSurface.rootFloat = some (1, eDom) := by
    unfold dataOfFront
    have hT2 : (ConstantInfo.defnInfo d).type = shift4LoopType := hty
    simp only [hmp, Option.bind_some, hx.rootFloat, hT2, hsd]
    with_unfolding_all rfl
  exact dataOfAt_of_pieces hval hx hfront (shift4Loop_dataOfCore lvl hlvl)

abbrev Shift4LoopExtern : Prop := RootExtern shift4LoopValue
abbrev Shift4LoopEnvFacts (env₀ : Environment) : Prop :=
  RootEnvFacts env₀ ``shift4Loop shift4LoopType shift4LoopValue shift4LoopValue shift4Loop.machineData ``Sparkle.Core.Signal.Signal.register

theorem shift4Loop_checkedEnv_of_finite (lvl : Lean.Expr → Nat) (env₀ : Environment)
    (hlvl : lvl shift4Loop.machineData.shape.body = 1000000) (hx : Shift4LoopExtern) (hf : Shift4LoopEnvFacts env₀) :
    CheckedEnv lvl env₀ ``shift4Loop shift4LoopType shift4LoopValue shift4Loop.machineData := by
  obtain ⟨d, hroot, hshape⟩ := hf.root
  obtain ⟨-, -, hty, hval⟩ := id hroot
  exact checkedEnv_of_inl hroot hshape hf.ui_val hf.ui_ty
    (shift4Loop_gates d hty hval _ hf.ip_val)
    (shift4Loop_gates { d with value := shift4LoopValue, type := shift4LoopType } rfl rfl _ hf.ip_inl)
    (shift4Loop_dataOfAt lvl hlvl { d with value := shift4LoopValue, type := shift4LoopType } rfl rfl _ hf.proj hx)

/-- **`shift4Loop_final11`**: `shift4Loop_final10` with `hchk : CheckedStart` replaced by the finite facts and the link `ReadsAt env₀ cref w` -/
theorem shift4Loop_final11 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``shift4Loop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAt ``shift4Loop mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hlvl : lvl shift4Loop.machineData.shape.body = 1000000) (hx : Shift4LoopExtern) (hf : Shift4LoopEnvFacts env₀)
    (hlink : ReadsAt env₀ cref w) :
    (∃ raw, PostRun mctx mref cctx cref w ``shift4Loop D' b raw) ∧
    ∃ (mm : MonoTy shShift4) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``shift4Loop D') ``shift4Loop shShift4 mm b D' p :=
  shift4Loop_final10 L lvl env₀ hstart hr hhead hcell ⟨shift4Loop_checkedEnv_of_finite lvl env₀ hlvl hx hf, hlink⟩

/-! ## counterEnableLoop -/

theorem counterEnableLoop_gates (d : DefinitionVal) (hty : d.type = counterEnableLoopType) (hval : d.value = counterEnableLoopValue)
    (ip : Lean.Expr → Bool) (hip : ip (peeledBody counterEnableLoopValue) = false) :
    (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true := by
  have hmp : mixedGatePeel counterEnableLoopValue = some ([(`en, MixedGateBinder.bool)], peeledBody counterEnableLoopValue) := by with_unfolding_all rfl
  constructor
  · unfold certifiedShape?
    simp only [hval]
    with_unfolding_all rfl
  · unfold mixedCertifiedShape?
    simp only [hval, hty, hmp]
    unfold unifiedInstanceRoot hierInstRoot
    simp only [hip, Bool.false_and, Bool.false_or]
    with_unfolding_all rfl

theorem counterEnableLoop_srcDomOf (se : StructEnv) (hf : se.proj ``Sparkle.Core.Signal.Signal.loop = none)
    (hfind : (peeledBody counterEnableLoopValue).find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8) = none) :
    srcDomOf se counterEnableLoopType (peeledBody counterEnableLoopValue) = some (eDom, 0) := by
  obtain ⟨ls, args, hs⟩ : ∃ ls args, inlSpine (peeledBody counterEnableLoopValue) [] = (Lean.Expr.const ``Sparkle.Core.Signal.Signal.loop ls, args) :=
    ⟨_, _, by with_unfolding_all rfl⟩
  have hm : machRunApp? (peeledBody counterEnableLoopValue) = none := by with_unfolding_all rfl
  have hroot := machRoot_of_head se.proj hs hf hm ⟨_, _, by with_unfolding_all rfl⟩
  unfold srcDomOf
  rw [hroot]
  simp only [hfind]
  with_unfolding_all rfl

theorem counterEnableLoop_dataOfCore (lvl : Lean.Expr → Nat) (hlvl : lvl counterEnableLoop.machineData.shape.body = 1000000) :
    dataOfCore lvl counterEnableLoop.machineData.shape 1 eDom = some counterEnableLoop.machineData := by
  unfold dataOfCore
  rw [hlvl]
  with_unfolding_all rfl

theorem counterEnableLoop_dataOfAt (lvl : Lean.Expr → Nat) (hlvl : lvl counterEnableLoop.machineData.shape.body = 1000000)
    (d : DefinitionVal) (hty : d.type = counterEnableLoopType) (hval : d.value = counterEnableLoopValue)
    (se : StructEnv) (hproj : se.proj ``Sparkle.Core.Signal.Signal.loop = none) (hx : RootExtern counterEnableLoopValue) :
    dataOfAt lvl (.defnInfo d) se counterEnableLoop.machineData.shape = some counterEnableLoop.machineData := by
  have hmp : mixedGatePeel counterEnableLoopValue = some ([(`en, MixedGateBinder.bool)], peeledBody counterEnableLoopValue) := by with_unfolding_all rfl
  have hsd := counterEnableLoop_srcDomOf se hproj hx.find
  have hfront : dataOfFront (.defnInfo d) se counterEnableLoop.machineData.shape counterEnableLoopValue Sparkle.Compiler.MachRawSurface.rootFloat = some (1, eDom) := by
    unfold dataOfFront
    have hT2 : (ConstantInfo.defnInfo d).type = counterEnableLoopType := hty
    simp only [hmp, Option.bind_some, hx.rootFloat, hT2, hsd]
    with_unfolding_all rfl
  exact dataOfAt_of_pieces hval hx hfront (counterEnableLoop_dataOfCore lvl hlvl)

abbrev CounterEnableLoopExtern : Prop := RootExtern counterEnableLoopValue
abbrev CounterEnableLoopEnvFacts (env₀ : Environment) : Prop :=
  RootEnvFacts env₀ ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoopValue counterEnableLoop.machineData ``Sparkle.Core.Signal.Signal.loop

theorem counterEnableLoop_checkedEnv_of_finite (lvl : Lean.Expr → Nat) (env₀ : Environment)
    (hlvl : lvl counterEnableLoop.machineData.shape.body = 1000000) (hx : CounterEnableLoopExtern) (hf : CounterEnableLoopEnvFacts env₀) :
    CheckedEnv lvl env₀ ``counterEnableLoop counterEnableLoopType counterEnableLoopValue counterEnableLoop.machineData := by
  obtain ⟨d, hroot, hshape⟩ := hf.root
  obtain ⟨-, -, hty, hval⟩ := id hroot
  exact checkedEnv_of_inl hroot hshape hf.ui_val hf.ui_ty
    (counterEnableLoop_gates d hty hval _ hf.ip_val)
    (counterEnableLoop_gates { d with value := counterEnableLoopValue, type := counterEnableLoopType } rfl rfl _ hf.ip_inl)
    (counterEnableLoop_dataOfAt lvl hlvl { d with value := counterEnableLoopValue, type := counterEnableLoopType } rfl rfl _ hf.proj hx)

/-- **`counterEnableLoop_final11`** -/
theorem counterEnableLoop_final11 {ι : Type} {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``counterEnableLoop) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAt ``counterEnableLoop mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hlvl : lvl counterEnableLoop.machineData.shape.body = 1000000) (hx : CounterEnableLoopExtern) (hf : CounterEnableLoopEnvFacts env₀)
    (hlink : ReadsAt env₀ cref w) :
    (∃ raw, PostRun mctx mref cctx cref w ``counterEnableLoop D' b raw) ∧
    ∃ (mm : MonoTy shEnable) (p : Pkg ι (fun _ => defaultDomain)),
      RootArtifactMono (envAt cref w)
        (genGP (ι := ι) (dom := fun _ => defaultDomain) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``counterEnableLoop D') ``counterEnableLoop shEnable mm b D' p :=
  counterEnableLoop_final10 L lvl env₀ hstart hr hhead hcell ⟨counterEnableLoop_checkedEnv_of_finite lvl env₀ hlvl hx hf, hlink⟩

/-! ## arbiterSignal (the inliner changes the value: the entry constant is the inlined declaration) -/

theorem arbiterSignal_gates_orig (d : DefinitionVal) (hty : d.type = arbiterType) (hval : d.value = arbiterValue)
    (ip : Lean.Expr → Bool) (hip : ip (peeledBody arbiterValue) = false) :
    (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true := by
  have hmp : mixedGatePeel arbiterValue = some ([(`dom, MixedGateBinder.domain), (`reqA, MixedGateBinder.bool), (`reqB, MixedGateBinder.bool)], peeledBody arbiterValue) := by with_unfolding_all rfl
  constructor
  · unfold certifiedShape?
    simp only [hval]
    with_unfolding_all rfl
  · unfold mixedCertifiedShape?
    simp only [hval, hty, hmp]
    unfold unifiedInstanceRoot hierInstRoot
    simp only [hip, Bool.false_and, Bool.false_or]
    with_unfolding_all rfl

theorem arbiterSignal_gates_inl (d : DefinitionVal) (hty : d.type = arbiterType) (hval : d.value = arbiterInlinedValue)
    (ip : Lean.Expr → Bool) (hip : ip (peeledBody arbiterInlinedValue) = false) :
    (certifiedShape? false [] (.defnInfo d)).isNone = true ∧ (mixedCertifiedShape? false [] (.defnInfo d) ip).isNone = true := by
  have hmp : mixedGatePeel arbiterInlinedValue = some ([(`dom, MixedGateBinder.domain), (`reqA, MixedGateBinder.bool), (`reqB, MixedGateBinder.bool)], peeledBody arbiterInlinedValue) := by with_unfolding_all rfl
  constructor
  · unfold certifiedShape?
    simp only [hval]
    with_unfolding_all rfl
  · unfold mixedCertifiedShape?
    simp only [hval, hty, hmp]
    unfold unifiedInstanceRoot hierInstRoot
    simp only [hip, Bool.false_and, Bool.false_or]
    with_unfolding_all rfl

theorem arbiterSignal_srcDomOf (se : StructEnv) (hf : se.proj ``Sparkle.Core.Signal.Signal.loop = none)
    (hfind : (peeledBody arbiterInlinedValue).find? (fun t => t.isAppOfArity ``Sparkle.Core.runCircuitH 8) = none) :
    srcDomOf se arbiterType (peeledBody arbiterInlinedValue) = some (Lean.Expr.bvar 2, 0) := by
  obtain ⟨ls, args, hs⟩ : ∃ ls args, inlSpine (peeledBody arbiterInlinedValue) [] = (Lean.Expr.const ``Sparkle.Core.Signal.Signal.loop ls, args) :=
    ⟨_, _, by with_unfolding_all rfl⟩
  have hm : machRunApp? (peeledBody arbiterInlinedValue) = none := by with_unfolding_all rfl
  have hroot := machRoot_of_head se.proj hs hf hm ⟨_, _, by with_unfolding_all rfl⟩
  unfold srcDomOf
  rw [hroot]
  simp only [hfind]
  with_unfolding_all rfl

theorem arbiterSignal_dataOfCore (lvl : Lean.Expr → Nat)
    (hlvl : lvl Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape.body = 1000000) :
    dataOfCore lvl Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape 3 (Lean.Expr.bvar 15) =
      some Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData := by
  unfold dataOfCore
  rw [hlvl]
  with_unfolding_all rfl

theorem arbiterSignal_dataOfAt (lvl : Lean.Expr → Nat)
    (hlvl : lvl Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape.body = 1000000)
    (d : DefinitionVal) (hty : d.type = arbiterType) (hval : d.value = arbiterInlinedValue)
    (se : StructEnv) (hproj : se.proj ``Sparkle.Core.Signal.Signal.loop = none) (hx : RootExtern arbiterInlinedValue) :
    dataOfAt lvl (.defnInfo d) se Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape =
      some Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData := by
  have hmp : mixedGatePeel arbiterInlinedValue = some ([(`dom, MixedGateBinder.domain), (`reqA, MixedGateBinder.bool), (`reqB, MixedGateBinder.bool)], peeledBody arbiterInlinedValue) := by with_unfolding_all rfl
  have hsd := arbiterSignal_srcDomOf se hproj hx.find
  have hfront : dataOfFront (.defnInfo d) se Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape arbiterInlinedValue Sparkle.Compiler.MachRawSurface.rootFloat = some (3, Lean.Expr.bvar 15) := by
    unfold dataOfFront
    have hT2 : (ConstantInfo.defnInfo d).type = arbiterType := hty
    simp only [hmp, Option.bind_some, hx.rootFloat, hT2, hsd]
    with_unfolding_all rfl
  exact dataOfAt_of_pieces hval hx hfront (arbiterSignal_dataOfCore lvl hlvl)

abbrev ArbiterSignalExtern : Prop := RootExtern arbiterInlinedValue
abbrev ArbiterSignalEnvFacts (env₀ : Environment) : Prop :=
  RootEnvFacts env₀ ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue arbiterInlinedValue
    Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData ``Sparkle.Core.Signal.Signal.loop

theorem arbiterSignal_checkedEnv_of_finite (lvl : Lean.Expr → Nat) (env₀ : Environment)
    (hlvl : lvl Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape.body = 1000000)
    (hx : ArbiterSignalExtern) (hf : ArbiterSignalEnvFacts env₀) :
    CheckedEnv lvl env₀ ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal arbiterType arbiterValue Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData := by
  obtain ⟨d, hroot, hshape⟩ := hf.root
  obtain ⟨-, -, hty, hval⟩ := id hroot
  exact checkedEnv_of_inl hroot hshape hf.ui_val hf.ui_ty
    (arbiterSignal_gates_orig d hty hval _ hf.ip_val)
    (arbiterSignal_gates_inl { d with value := arbiterInlinedValue, type := arbiterType } rfl rfl _ hf.ip_inl)
    (arbiterSignal_dataOfAt lvl hlvl { d with value := arbiterInlinedValue, type := arbiterType } rfl rfl _ hf.proj hx)

/-- **`arbiterSignal_final11`** (keeps `hB0`/`hcont`: the boundary rows are an existence statement `ReadsAt` does not carry) -/
theorem arbiterSignal_final11 {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (lvl : Lean.Expr → Nat) (env₀ : Environment)
    {mctx : Meta.Context} {cctx : Core.Context} {w w' : Void IO.RealWorld} {b : Sparkle.IR.AST.Module} {D' : Sparkle.IR.AST.Design}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (Sparkle.Compiler.Elab.synthesizeCombinational ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal) mctx mref cctx cref w (b, D') w')
    (hhead : HeadAt ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal mctx mref cctx cref w) (hcell : ReadWorld cref)
    (hlvl : lvl Sparkle.IP.Arbiter.RoundRobin.arbiterSignal.machineData.shape.body = 1000000)
    (hx : ArbiterSignalExtern) (hf : ArbiterSignalEnvFacts env₀)
    (hlink : ReadsAt env₀ cref w)
    (hB0 : BoundaryRowsInEnv env₀) (hcont : ContainsAt env₀ cref w boundaryNames) :
    (∃ raw, PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D' b raw) ∧
    ∃ (mm : shArbiter.Ty) (p : Pkg DomainConfig (fun i => i)),
      RootArtifact (envAt cref w)
        (genGP (ι := DomainConfig) (dom := fun i => i) lvl (Tools.ShippingGen5SM1.dataOfSound_initsOf lvl) (canonGD lvl) (envAt cref w))
        (PostRun mctx mref cctx cref w ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal D') ``Sparkle.IP.Arbiter.RoundRobin.arbiterSignal shArbiter mm b D' p :=
  arbiterSignal_final10 L lvl env₀ hstart hr hhead hcell ⟨arbiterSignal_checkedEnv_of_finite lvl env₀ hlvl hx hf, hlink⟩ hB0 hcont

end Tools.ShippingFGCircuitS1nRoots

#print axioms Tools.ShippingFGCircuitS1nRoots.shift4Loop_checkedEnv_of_finite
#print axioms Tools.ShippingFGCircuitS1nRoots.counterEnableLoop_checkedEnv_of_finite
#print axioms Tools.ShippingFGCircuitS1nRoots.arbiterSignal_checkedEnv_of_finite
#print axioms Tools.ShippingFGCircuitS1nRoots.shift4Loop_final11
#print axioms Tools.ShippingFGCircuitS1nRoots.counterEnableLoop_final11
#print axioms Tools.ShippingFGCircuitS1nRoots.arbiterSignal_final11
