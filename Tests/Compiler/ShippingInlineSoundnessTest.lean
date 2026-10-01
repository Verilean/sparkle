import Tools.ShippingInlineSoundness
import Tests.Compiler.ShippingMixedExecutionTest

/-! Front-end normalisation (unfolding of user definitions) at the real entry.

A declaration written with helper definitions misses the certified gates as
written; the entry hands on its ENTRY CONSTANT — the declaration with the
helpers unfolded — when that passes a gate.  The tests check, on the real
compiler: which declarations are unfolded and which are not, that the
certified compile of the unfolding is byte-identical to the legacy compile of
the original (which unfolds at the call site), and two end-to-end theorems on
real helper-structured declarations. -/
namespace Sparkle.Tests.Compiler.ShippingInlineSoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingUnifiedSource
open Tools.ShippingMixedSourceBridge Tools.ShippingMixedExecutionSoundness
open Tools.ShippingInlineSoundness

/-! ## Helpers and the declarations that use them -/

def add2 {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a + b
def idh {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a
def lit5 {dom : DomainConfig} (_a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.pure 5#8
def add3 {dom : DomainConfig} (a b c : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  add2 (add2 a b) c
def sel {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := Signal.mux c (a + b) (a - b)
def regh {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.register 0#8 x
def ltb {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom Bool := Signal.ult a b
def accx {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.loop fun s => Signal.register 0#8 (s + x)
def addw {dom : DomainConfig} {n : Nat} (a b : Signal dom (BitVec n)) : Signal dom (BitVec n) :=
  a + b
def step8 {dom : DomainConfig} (c : Signal dom Bool) (s a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := Signal.mux c s a + b

-- A helper at the root, inside a cone, repeated, a literal, the identity,
-- nested helpers, both sorts, around a register and a loop, at a concrete
-- domain, width-generic, and helpers as each other's arguments.
def uRoot {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := add2 a b
def uCone {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  add2 a b + a
def uTwice {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  add2 a b + add2 a b
def uLit {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  lit5 a + lit5 a
def uId {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := idh a + b
def uNest {dom : DomainConfig} (a b c : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  add3 a b c * a
def uMux {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := sel c a b + sel c b a
def uReg {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  regh (add2 a b)
def uCmp {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.mux (ltb a b) (add2 a b) (idh a)
def uIdRoot {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := idh a
def uLitRoot {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := lit5 a
def uShare {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  add2 a b + (a + b)
def uLoop {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  accx (add2 a b)
def uBool {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom Bool :=
  ltb (add2 a b) b
def uConcrete (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) :=
  add2 a b + add2 b a
def uGeneric {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  addw a b + a
def uArgs {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  add2 (lit5 a) (lit5 b)

/-- The end-to-end combinational witness: helpers of both sorts, nested. -/
def useSel {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) :=
  Signal.mux (ltb (add2 a b) b) (sel c a b) (add3 a b a)

/-- The end-to-end sequential witness: a helper INSIDE the feedback loop. -/
def accH {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) :=
  Signal.loop (fun s => Signal.register 0#8 (step8 c s a b))

/-! ## What must NOT be unfolded -/

/-- A user definition whose last name component the legacy dispatcher
intercepts (`handleMux` matches every `….mux`). -/
def Shadow.mux {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := Signal.mux c a b
def uShadow {dom : DomainConfig} (c : Signal dom Bool) (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := Shadow.mux c a b + a

@[hardware_module]
def childTag {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := a + b
def uTagged {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  childTag a b

/-- Doubling, nested deep enough that the unfolded TREE exceeds the node
budget (the legacy translator shares the operand through its cache). -/
def dbl {dom : DomainConfig} (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := x + x
def uDeep {dom : DomainConfig} (a : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl (dbl
    (dbl (dbl (dbl (dbl a)))))))))))))))))))))

/-! ## The combinational endpoint on a helper-structured declaration -/

def useSelTerm : Term (.bits 8) := .mux
  (.compare .ult (.binary .add (.bitsInput 8 0) (.bitsInput 8 1)) (.bitsInput 8 1))
  (.mux (.boolInput 0) (.binary .add (.bitsInput 8 0) (.bitsInput 8 1))
    (.binary .sub (.bitsInput 8 0) (.bitsInput 8 1)))
  (.binary .add (.binary .add (.bitsInput 8 0) (.bitsInput 8 1)) (.bitsInput 8 0))

theorem useSelTerm_wf : useSelTerm.WF 1 2 (fun _ => 8) := by simp [useSelTerm, Term.WF]

/-- The kernel's own delta/beta: the declaration, helpers and all, IS the
denotation of the unfolded term. -/
theorem useSel_library {D : DomainConfig} (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    denote bi vi useSelTerm = useSel (bi 0) (vi 0 8) (vi 1 8) := rfl

#def_entry_value useSelEntry of useSel
def useSelBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
theorem useSel_peel : mixedGatePeel useSelEntry = some (useSelBinders,
    quote (.bvar 3) (fun _ => inputExpr useSelBinders.length 1)
      (fun j => inputExpr useSelBinders.length (j + 2)) useSelTerm) := rfl

/-- **Source-to-RTL execution of a helper-structured declaration.** From the
real `synthesizeCombinational` run and the entry-constant boundary, the
compiled module computes the declaration's own stream — `useSel` as written,
with its helpers. -/
theorem useSel_execution {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinational ``useSel) mctx mref cctx cref w (m, design) w')
    (entry : EntryDefines mctx mref cctx cref ``useSel useSelEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = useSelBinders.length ∧
    ∃ cache : IO.Ref (ExprStructMap String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (tick : Nat) (initial : Env) (mems : MEnv),
      SourceInputs ``useSel useSelBinders ids cache
        (fun j => (bools j).val tick) (fun j n => (bits j n).val tick) initial →
      ExecutionValue m initial mems
        ((useSel (bools 1) (bits 2 8) (bits 3 8)).val tick).toNat := by
  apply execution_source_of_entry (kb := 1) (kv := 2) (vw := fun _ => 8)
    (bpos := fun _ => 1) (vpos := fun j => j + 2) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) useSel_peel useSelTerm_wf
  · intro j hj
    have h : j = 0 := by omega
    subst h
    exact ⟨`c, rfl⟩
  · intro j hj
    have h : j = 0 ∨ j = 1 := by omega
    rcases h with rfl | rfl
    · exact ⟨`a, rfl⟩
    · exact ⟨`b, rfl⟩

/-! ## The sequential endpoint: a helper inside the feedback loop -/

def accHTerm : Term (.bits 8) := .binary .add
  (.mux (.boolInput 0) (.bitsInput 8 2) (.bitsInput 8 0)) (.bitsInput 8 1)

theorem accHTerm_wf : accHTerm.WF 1 3 (fun _ => 8) := by simp [accHTerm, Term.WF]

#def_entry_value accHEntry of accH
def accHBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`c, .bool), (`a, .bits 8), (`b, .bits 8)]
def accHInst : Lean.Expr :=
  .app (.const ``BitVec.instInhabited []) (Tools.ShippingEntrySoundness.natE 8)
theorem accH_peel : mixedGatePeel accHEntry = some (accHBinders,
    Tools.ShippingRegisterSoundness.loopRegisterE
      (inputExpr accHBinders.length 0) (inputExpr (accHBinders.length + 1) 0)
      accHInst 8 0
      (quote (inputExpr (accHBinders.length + 1) 0)
        (fun _ => inputExpr (accHBinders.length + 1) 1)
        (fun j => if j = 2 then .bvar 0 else inputExpr (accHBinders.length + 1) (j + 2))
        accHTerm)) := rfl

/-- **The whole trace of a helper-structured feedback register.** The
compiled module's `runModule` trace observes the source stream of `accH` as
written — `Signal.loop` over a register whose next state is a helper call. -/
theorem accH_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``accH [] false) mctx mref cctx cref wst
      (m, design) wst')
    (entry : EntryDefines mctx mref cctx cref ``accH accHEntry) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = accHBinders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ {D : DomainConfig} (bools : Nat → Signal D Bool)
        (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat),
      (∀ t stv, SourceInputs ``accH accHBinders ids cache
          (fun i => (bools i).val (k - 1 - t)) (fun i n => (bits i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r = 0 →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((accH (bools 1) (bits 2 8) (bits 3 8)).val j).toNat := by
  have packaged := loopRegister_run_of_entry (kb := 1) (kv := 2)
    (vw := fun _ => 8) (bpos := fun _ => 1) (vpos := fun j => j + 2) hr entry
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) accH_peel
    (by simp [accHBinders]) rfl accHTerm_wf (by decide)
    (by
      intro j hj
      have h : j = 0 := by omega
      subst h
      exact ⟨`c, rfl⟩)
    (by
      intro j hj
      have h : j = 0 ∨ j = 1 := by omega
      rcases h with rfl | rfl
      · exact ⟨`a, rfl⟩
      · exact ⟨`b, rfl⟩)
  obtain ⟨ids, nd, len, cache, r, H⟩ := packaged
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro D bools bits mems k seed st0 hseed hst0
  have hcone : ∀ (s₁ s₂ : Signal D (BitVec 8)) (t : Nat), s₁.val t = s₂.val t →
      (Signal.mux (bools 1) s₁ (bits 2 8) + bits 3 8).val t =
      (Signal.mux (bools 1) s₂ (bits 2 8) + bits 3 8).val t := by
    intro s1 s2 t h
    show (if (bools 1).val t then s1.val t else (bits 2 8).val t) + (bits 3 8).val t = _
    rw [h]
    rfl
  have hv := Tools.ShippingRegisterSoundness.loop_register_val (0#8)
    (fun s => Signal.mux (bools 1) s (bits 2 8) + bits 3 8) hcone
  -- The kernel's own delta/beta: the helper inside the loop unfolds.
  have hacc : accH (bools 1) (bits 2 8) (bits 3 8) =
      Signal.loop (fun s => Signal.register 0#8
        (Signal.mux (bools 1) s (bits 2 8) + bits 3 8)) := rfl
  apply H (fun wall i => (bools i).val wall) (fun wall i n => (bits i n).val wall)
    mems k seed st0
    (fun j => ((accH (bools 1) (bits 2 8) (bits 3 8)).val j).toNat)
    hseed (by rw [hst0]; decide)
  · rw [hst0, hacc]
    rw [show (Signal.loop (fun s => Signal.register 0#8
      (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))).val 0 = 0#8 from hv.1]
    rfl
  · intro j hj
    rw [hacc]
    rw [show (Signal.loop (fun s => Signal.register 0#8
      (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))).val (j + 1) =
      (Signal.mux (bools 1) (Signal.loop (fun s => Signal.register 0#8
        (Signal.mux (bools 1) s (bits 2 8) + bits 3 8))) (bits 2 8) + bits 3 8).val j
      from hv.2 j]
    show ((if (bools 1).val j then _ else (bits 2 8).val j) + (bits 3 8).val j).toNat = _
    cases hc : (bools 1).val j <;>
      simp [eval, accHTerm, Tools.ShippingScalarSoundness.Binary.apply, hc,
        BitVec.ofNat_toNat]

/-! ## Runtime gates on the real compiler -/

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  let translate : TranslateFn := fun e h t n => translateExprToWire e h t n
  let mut unfolded := 0
  for name in [``uRoot, ``uCone, ``uTwice, ``uLit, ``uId, ``uNest, ``uMux, ``uReg, ``uCmp,
      ``uIdRoot, ``uLitRoot, ``uShare, ``uLoop, ``uBool, ``uConcrete, ``uGeneric, ``uArgs,
      ``useSel, ``accH] do
    let ci ← getConstInfo name
    -- As written, the declaration misses both gates …
    unless (certifiedShape? false [] ci).isNone && (mixedCertifiedShape? false [] ci pred).isNone do
      throwError "{name}: a helper-structured declaration passed a gate as written"
    -- … the entry constant is its unfolding, and a gate accepts it.
    let ec := entryConst true false [] ci pred inl
    unless ec.value? == (inlinedConst inl ci).value? && ec.value? != ci.value? do
      throwError "{name}: the entry constant is not the unfolding"
    unless (certifiedShape? false [] ec).isSome || (mixedCertifiedShape? false [] ec pred).isSome do
      throwError "{name}: no gate accepts the unfolding"
    -- The certified compile of the unfolding is byte-identical to the legacy
    -- compile of the original, which unfolds at the call site.
    let (mc, dc) ← synthesizeCombinationalCore name [] false
    let (ml, dl) ← synthesizeCombinationalCoreWith translate name [] false
      (certifiedFrontEnd := false)
    unless mc.body == ml.body && mc.inputs == ml.inputs && mc.outputs == ml.outputs &&
        mc.wires == ml.wires && mc.name == ml.name && dc.modules == dl.modules do
      throwError "{name}: the unfolded certified compile departed from the legacy compile"
    unfolded := unfolded + 1
  unless unfolded == 19 do throwError "unfolding case count mismatch: {unfolded}"
  logInfo m!"INLINE FRONT END: {unfolded} helper-structured declarations unfolded, certified == legacy bytes"

run_cmd liftTermElabM do
  let env ← getEnv
  let pred := instancePredicate env
  let inl := userInliner env
  -- The values the theorems name ARE the entry constants of this environment.
  -- (Compared as reflected terms: the named definitions are the reflection
  -- of the entry constant's value.)
  for (name, valueName) in [(``useSel, ``useSelEntry), (``accH, ``accHEntry)] do
    let some v := (entryConst true false [] (← getConstInfo name) pred inl).value?
      | throwError "{name} has no entry value"
    let .ok r := Tools.ShippingEntrySoundness.reflExpr v
      | throwError "{name}: entry value is not reflectable"
    unless (← getConstInfo valueName).value? == some r do
      throwError "{valueName} is not the entry constant of {name}"
  -- Not unfolded: a name the legacy dispatcher intercepts, a tagged module,
  -- library definitions.
  unless (userDefinition? env ``Shadow.mux).isNone do
    throwError "a reserved-suffix definition is unfolded"
  unless (userDefinition? env ``childTag).isNone do
    throwError "a tagged module is unfolded"
  unless (userDefinition? env ``Sparkle.Core.Signal.Signal.register).isNone &&
      (userDefinition? env ``Sparkle.Core.Signal.Signal.mux).isNone &&
      (userDefinition? env ``HAdd.hAdd).isNone do
    throwError "a library definition is unfolded"
  unless (userDefinition? env ``add2).isSome do throwError "a plain helper is not unfolded"

/-- Default-entry and legacy-front-end compiles agree, and the entry constant
is the declaration as read. -/
def checkLeftAlone (name : Name) : MetaM Sparkle.IR.AST.Design := do
  let env ← getEnv
  let ci ← getConstInfo name
  unless (entryConst true false [] ci (instancePredicate env) (userInliner env)).value? ==
      ci.value? do
    throwError "{name} was rewritten"
  let (m, d) ← synthesizeCombinationalCore name [] false
  let (ml, _) ← synthesizeCombinationalCoreWith
    (fun e h t n => translateExprToWire e h t n) name [] false (certifiedFrontEnd := false)
  unless m.body == ml.body && m.wires == ml.wires do
    throwError "{name}: default and legacy compiles differ"
  return d

run_cmd liftTermElabM do
  -- A declaration whose only helper is not unfoldable keeps the legacy route,
  -- unchanged.
  let _ ← checkLeftAlone ``uShadow
  -- A tagged child stays an instance (the instance gate, not the unfolding).
  let dt ← checkLeftAlone ``uTagged
  unless dt.modules.length == 1 do throwError "uTagged lost its child module"
  -- Past the node budget the unfolding is abandoned and the legacy route
  -- compiles the original.
  let some vD := (← getConstInfo ``uDeep).value? | throwError "uDeep has no value"
  unless userInliner (← getEnv) vD == vD do throwError "uDeep was unfolded past the budget"
  let _ ← checkLeftAlone ``uDeep
  logInfo "INLINE FRONT END: reserved, tagged, library and over-budget definitions left alone"

run_cmd do
  if (← get).messages.hasErrors then throwError "inline front-end regression failed"
  for name in [``Tools.ShippingInlineSoundness.synthesizeCombinationalCore_entry_sound,
      ``Tools.ShippingInlineSoundness.EntryDefines.of_env,
      ``Tools.ShippingInlineSoundness.EntryDefines.of_inline,
      ``Tools.ShippingInlineSoundness.execution_source_of_entry,
      ``Tools.ShippingInlineSoundness.loopRegister_step_of_entry,
      ``Tools.ShippingInlineSoundness.loopRegister_run_of_entry,
      ``Tools.ShippingEntrySoundness.entryConst_inlined,
      ``Tools.ShippingEntrySoundness.synthesizeCombinationalCore_reads,
      ``useSel_library, ``useSel_execution, ``accH_run] do
    for ax in (← liftCoreM <| collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected inline front-end axiom: {name}: {ax}"
  logInfo "INLINE FRONT END ENDPOINTS: entry-constant bundle, combinational and feedback-register endpoints on helper-structured declarations; standard axioms only"

end Sparkle.Tests.Compiler.ShippingInlineSoundnessTest
