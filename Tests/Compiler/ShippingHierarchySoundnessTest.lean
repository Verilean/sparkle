import Tools.ShippingHierarchySoundness
import Tools.ShippingInstanceEntrySoundness
import Sparkle.Compiler.Elab

/-! S6-1 hierarchy foundation tests: a real `@[hardware_module]` child and
its instantiating parent, both compiled modules pinned byte-for-byte to
the canonical single-instance shape, the linked-instance semantics
exercised numerically, and the linked endpoint instantiated with a
standard-axioms audit. -/
namespace Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
open Lean Elab Command Meta Sparkle.Compiler.Elab Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness
open Tools.ShippingInstanceEntrySoundness
open Tools.ShippingEntrySoundness (EnvDefines RunsTo)
open Tools.ShippingMixedSourceBridge (inputExpr)

@[hardware_module] def childAdd {dom : DomainConfig}
    (x y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := x + y

def parentUse {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd a b

/-- A multi-output child: its instantiating parent must STAY on the legacy
front end (the certified single-output harness would drop `hi`). -/
structure TwoOut (dom : DomainConfig) where
  lo : Signal dom (BitVec 8)
  hi : Signal dom (BitVec 8)

@[hardware_module] def childTwo {dom : DomainConfig}
    (x y : Signal dom (BitVec 8)) : TwoOut dom :=
  { lo := x + y, hi := x - y }

def parentTwo {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : TwoOut dom :=
  childTwo a b

/-- A sequential child: the certified instance path must agree with the
legacy front end byte-for-byte, including the clk/rst auto-plumbing. -/
@[hardware_module] def childSeq {dom : DomainConfig}
    (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.register 0#8 x

def parentSeq {dom : DomainConfig} (a : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childSeq a

/-- The child module the pipeline emits, pinned literally. -/
def childModule : Sparkle.IR.AST.Module :=
  { name := "childAdd"
    inputs := [⟨"_gen_x", .bitVector 8⟩, ⟨"_gen_y", .bitVector 8⟩]
    outputs := [⟨"out", .bitVector 8⟩]
    wires := [⟨"_gen_x", .bitVector 8⟩, ⟨"_gen_y", .bitVector 8⟩,
      ⟨"_gen_out", .bitVector 8⟩]
    body := [.assign "_gen_out" (.op .add [.ref "_gen_x", .ref "_gen_y"]),
      .assign "out" (.ref "_gen_out")]
    parameters := [] }

def childWe : WEnv := fun n =>
  if n == "_gen_x" || n == "_gen_y" || n == "_gen_out" || n == "out" then 8 else 0

def childrenOf (mn : String) : String → Option (Sparkle.IR.AST.Module × WEnv) :=
  fun n => if n = mn then some (childModule, childWe) else none

/-- **The linked endpoint on the canonical parent shape**: the parent's
linked elaboration observes the source composition `childAdd a b` —
the parent SOURCE is literally that composition. Generic in the
instance/module names the emitter generated. -/
theorem parentUse_linked {we : WEnv} {mems : MEnv} {D : DomainConfig}
    (mn instName : String)
    (aS bS : Signal D (BitVec 8)) (t : Nat) (env0 : Env)
    (ha : env0 "_gen_a" = ((aS.val t).toNat))
    (hb : env0 "_gen_b" = ((bS.val t).toNat)) :
    ∃ envF, evalAssignsH we (childrenOf mn) mems
      (instBody mn instName
        [("_gen_x", .ref "_gen_a"), ("_gen_y", .ref "_gen_b")]
        "out" "_gen_out") env0 = some envF ∧
      envF "out" = ((parentUse aS bS).val t).toNat := by
  have hchild : childrenOf mn mn = some (childModule, childWe) := by
    simp [childrenOf]
  have hrun : evalAssigns childWe mems childModule.body
      (connEnv [("_gen_x", Sparkle.IR.AST.Expr.ref "_gen_a"),
        ("_gen_y", Sparkle.IR.AST.Expr.ref "_gen_b"),
        ("out", Sparkle.IR.AST.Expr.ref "_gen_out")] env0) =
      some (fun n =>
        if n = "out" then mask 8 (env0 "_gen_a" + env0 "_gen_b")
        else if n = "_gen_out" then mask 8 (env0 "_gen_a" + env0 "_gen_b")
        else connEnv [("_gen_x", Sparkle.IR.AST.Expr.ref "_gen_a"),
          ("_gen_y", Sparkle.IR.AST.Expr.ref "_gen_b"),
          ("out", Sparkle.IR.AST.Expr.ref "_gen_out")] env0 n) := rfl
  obtain ⟨envF, hev, hout, -⟩ := instBody_linked (we := we) (mems := mems)
    (mn := mn) (instName := instName)
    (inConns := [("_gen_x", .ref "_gen_a"), ("_gen_y", .ref "_gen_b")])
    (childOut := "out") (outW := "_gen_out")
    hchild rfl (by decide) hrun (by decide)
  refine ⟨envF, hev, ?_⟩
  rw [hout]
  show mask 8 (env0 "_gen_a" + env0 "_gen_b") = _
  rw [ha, hb]
  show (((aS.val t).toNat) + ((bS.val t).toNat)) % 2 ^ 8 =
    ((aS.val t + bS.val t)).toNat
  rw [BitVec.toNat_add]

/-! The S6-2 entry endpoint on the real parent declaration. -/

#def_decl_value parentUseValue of parentUse

def parentUseBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]

/-- The parent's own elaborated value IS the canonical two-input instance
call on the tagged child, byte for byte. -/
theorem parentUse_peel : mixedGatePeel parentUseValue = some (parentUseBinders,
    instE2 ``childAdd []
      (inputExpr parentUseBinders.length 0) (inputExpr parentUseBinders.length 1)
      (inputExpr parentUseBinders.length 2)) := rfl

/-- **The instance entry contract on the real parent**: under the run's
environment boundaries (its declaration table, its `@[hardware_module]`
tags and the scalar result type), the compiled parent/design pair
satisfies `InstancePreserves` — the parent module is the canonical
`instBody` over the pinned child compile and the design holds exactly
that child. -/
theorem parentUse_instance_entry {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``parentUse [] false)
      mctx mref cctx cref w (m, d) w')
    (env : EnvDefines mctx mref cctx cref ``parentUse parentUseValue)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment)
      mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e ``childAdd = true)
    (hscalar : ∀ dv : Lean.DefinitionVal, dv.value = parentUseValue →
      mixedGateResultScalar dv.type = true) :
    InstancePreserves ``parentUse parentUseBinders
      (instE2 ``childAdd []
        (inputExpr parentUseBinders.length 0) (inputExpr parentUseBinders.length 1)
        (inputExpr parentUseBinders.length 2)) m d :=
  instance_entry_of_env hr env tag
    (fun dv hv => by simp only [certifiedShape?, hv]; rfl)
    hscalar parentUse_peel rfl rfl rfl

open Sparkle.IR.AST in
run_cmd liftTermElabM do
  -- The compiled parent and child are EXACTLY the canonical shapes.
  let (mp, d) ← synthesizeCombinationalCore ``parentUse [] false
  unless d.modules.length == 1 do
    throwError "hierarchical design departed from one child: {d.modules.map (·.name)}"
  let some cm := d.modules.head? | throwError "no child module"
  unless cm.body == childModule.body && cm.inputs == childModule.inputs &&
      cm.outputs == childModule.outputs && cm.wires == childModule.wires do
    throwError "child module departed from the pinned shape"
  let [Stmt.inst mn instName conns, Stmt.assign outL (.ref outR)] := mp.body |
    throwError "parent body departed from the two-statement instance shape"
  unless mn == cm.name && outL == "out" && outR == "_gen_out" &&
      conns == [("_gen_x", .ref "_gen_a"), ("_gen_y", .ref "_gen_b"),
        ("out", .ref "_gen_out")] do
    throwError "parent instance connections departed from the canonical shape"
  unless mp.body == instBody mn instName
      [("_gen_x", .ref "_gen_a"), ("_gen_y", .ref "_gen_b")] "out" "_gen_out" do
    throwError "parent body is not the canonical instBody"
  -- The sub-module IS the child declaration's own certified compile,
  -- byte for byte, and the child passes the certified combinational
  -- gate — so the child-side combinational endpoints apply verbatim to
  -- the instantiated module.
  let (mc, _) ← synthesizeCombinationalCore ``childAdd [] false
  unless mc.body == cm.body && mc.wires == cm.wires &&
      mc.inputs == cm.inputs && mc.outputs == cm.outputs do
    throwError "sub-module departed from the child's standalone compile"
  unless (mixedCertifiedShape? false [] (← getConstInfo ``childAdd)).isSome do
    throwError "child declaration missed the certified gate"
  -- 16-case numeric regression of the LINKED semantics against Nat add.
  let weP : WEnv := fun n =>
    if n == "_gen_a" || n == "_gen_b" || n == "_gen_out" || n == "out" then 8 else 0
  let mut count : Nat := 0
  for av in List.range 4 do
    for bv in List.range 4 do
      let a := (63 * av + 11) % 256
      let b := (97 * bv + 5) % 256
      let env0 : Env := fun n =>
        if n == "_gen_a" then a else if n == "_gen_b" then b else 0
      let some envF := evalAssignsH weP (childrenOf mn) (fun _ _ => 0) mp.body env0 |
        throwError "linked elaboration failed at {a},{b}"
      unless envF "out" == (a + b) % 256 do
        throwError "linked out mismatch at {a},{b}: {envF "out"}"
      count := count + 1
  unless count == 16 do throwError "hier case count mismatch"
  -- The instance gate: the canonical parent is ACCEPTED at the run's
  -- predicate (it now routes through the certified front end), and the
  -- certified dispatch agrees with the legacy front end byte-for-byte.
  let pred := instancePredicate (← getEnv)
  unless (mixedCertifiedShape? false [] (← getConstInfo ``parentUse) pred).isSome do
    throwError "canonical parent missed the instance gate"
  let (mpL, dpL) ← synthesizeCombinationalCoreWith
    (fun e h t n => translateExprToWire e h t n) ``parentUse [] false
    (certifiedFrontEnd := false)
  unless mp.body == mpL.body && mp.inputs == mpL.inputs && mp.outputs == mpL.outputs &&
      mp.wires == mpL.wires && d.modules == dpL.modules do
    throwError "certified instance lowering departed from the legacy front end"
  -- Sequential child: gate-accepted, and certified/legacy parity holds
  -- including clk/rst plumbing.
  unless (mixedCertifiedShape? false [] (← getConstInfo ``parentSeq) pred).isSome do
    throwError "sequential-child parent missed the instance gate"
  let (ms, ds) ← synthesizeCombinationalCore ``parentSeq [] false
  let (msL, dsL) ← synthesizeCombinationalCoreWith
    (fun e h t n => translateExprToWire e h t n) ``parentSeq [] false
    (certifiedFrontEnd := false)
  unless ms.body == msL.body && ms.inputs == msL.inputs && ms.outputs == msL.outputs &&
      ms.wires == msL.wires && ds.modules == dsL.modules do
    throwError "sequential-child certified lowering departed from the legacy front end"
  -- Record-result parent: the scalar-result guard must keep it on the
  -- legacy path, which preserves BOTH outputs.
  unless (mixedCertifiedShape? false [] (← getConstInfo ``parentTwo) pred).isNone do
    throwError "record-result parent leaked through the instance gate"
  let (mt, _) ← synthesizeCombinationalCore ``parentTwo [] false
  unless mt.outputs.map (·.name) == ["lo", "hi"] do
    throwError "record-result parent lost an output: {mt.outputs.map (·.name)}"
  -- The retained scalar-type premise HOLDS for the real declaration.
  unless mixedGateResultScalar (← getConstInfo ``parentUse).type do
    throwError "parentUse's result type is not one scalar Signal"
  -- Axiom audit.
  for name in [``Tools.ShippingHierarchySoundness.instBody_linked,
      ``Tools.ShippingHierarchySoundness.connEnv_at,
      ``Tools.ShippingInstanceEntrySoundness.instance_term_gate,
      ``Tools.ShippingInstanceEntrySoundness.instance_step,
      ``Tools.ShippingInstanceEntrySoundness.instanceUncached_run,
      ``Tools.ShippingInstanceEntrySoundness.synthesizeMixedCertified_instance_sound,
      ``Tools.ShippingInstanceEntrySoundness.synthesizeFromConst_instance_sound,
      ``Tools.ShippingInstanceEntrySoundness.synthesizeCombinationalCore_instance_sound,
      ``Tools.ShippingInstanceEntrySoundness.instance_entry_of_env,
      ``parentUse_peel, ``parentUse_instance_entry,
      ``parentUse_linked] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected hierarchy soundness axiom: {name}: {ax}"
  logInfo "HIERARCHY FOUNDATION: canonical parent/child pinned; linked semantics matches; standard axioms only"

end Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
