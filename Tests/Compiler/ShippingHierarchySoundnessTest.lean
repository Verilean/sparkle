import Tools.ShippingHierarchySoundness
import Tools.ShippingInstanceEntrySoundness
import Tools.ShippingHierTermSoundness
import Tools.ShippingRegisterSoundness
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
open Tools.ShippingMixedSourceBridge (inputExpr SourceInputs)
open Tools.ShippingUnifiedSource
open Tools.ShippingRegisterSoundness (registerE)
open Tools.ShippingUnifiedMeaning Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx Tools.ShippingInstanceLeaf Tools.ShippingHierTermSoundness

@[hardware_module] def childAdd {dom : DomainConfig}
    (x y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := x + y

def parentUse {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd a b

/-- A three-input child and its parent: the n-ary instance contract. -/
@[hardware_module] def childAdd3 {dom : DomainConfig}
    (x y z : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := x + y + z

def parentUse3 {dom : DomainConfig} (a b c : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd3 a b c

/-- A two-data-port SEQUENTIAL child and its parent: the general
single-output contract (any arity, with clk/rst). -/
@[hardware_module] def childSeq2 {dom : DomainConfig}
    (x y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.register 0#8 (x + y)

def parentSeq2 {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childSeq2 a b

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

/-- Projection parents of the multi-output child: each selects ONE field of
the record-returning call, so the result is one scalar Signal and the parent
takes the certified projection arm. -/
def parentLo {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := (childTwo a b).lo

def parentHi {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := (childTwo a b).hi

/-- Cones over instance leaves: the parent computes on child results. -/
def parentMix {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd a b + a

def parentTwoCalls {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd a b + childAdd b a

def parentRepeat {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd a b + childAdd a b

def parentCmp {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom Bool := Signal.ult (childAdd a b) a

/-- A module PIPELINE: an instance call whose operand is an instance call. -/
def parentNested {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd (childAdd a b) b

/-- A WIDTH-GENERIC child. A hardware module is compiled once, at the
width its standalone compile infers (8 for a free width), not per call
site: instantiating it at any other width is refused by the width-linkage
check instead of being connected across mismatching widths. -/
@[hardware_module] def childW {dom : DomainConfig} (w : Nat)
    (x y : Signal dom (BitVec w)) : Signal dom (BitVec w) := x + y

def parentW8 {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childW 8 a b

def parentW16 {dom : DomainConfig} (a b : Signal dom (BitVec 16)) :
    Signal dom (BitVec 16) := childW 16 a b

/-- Every instance statement of a compiled parent is width-linked against
its child in the emitted design (the executable form of `InstsLinked`). -/
def designLinked (m : Sparkle.IR.AST.Module) (d : Sparkle.IR.AST.Design) : Bool :=
  m.body.all fun st =>
    match st with
    | .inst mn _ conns =>
      match d.modules.find? (fun c => c.name == mn) with
      | some c => instLinked m c conns
      | none => false
    | _ => true

/-- A sequential child: the certified instance path must agree with the
legacy front end byte-for-byte, including the clk/rst auto-plumbing. -/
@[hardware_module] def childSeq {dom : DomainConfig}
    (x : Signal dom (BitVec 8)) : Signal dom (BitVec 8) :=
  Signal.register 0#8 x

def parentSeq {dom : DomainConfig} (a : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childSeq a

/-- A sequential child INSIDE a cone: gate-accepted, byte-gated against the
legacy front end (the leaf contract itself covers combinational children). -/
def parentSeqMix {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childSeq a + b

/-- Further gate-accepted shapes, byte-gated against the legacy front end:
a sequential stage fed by a combinational one, a projection as a cone leaf,
and a projection as a call operand. -/
def parentPipeSeq {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childSeq (childAdd a b)

def parentProjLeaf {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := (childTwo a b).lo + a

def parentProjArg {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd (childTwo a b).lo b

/-- The child module the pipeline emits, pinned literally. -/
def childModule : Sparkle.IR.AST.Module :=
  { name := "Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.childAdd"
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

/-! The one-input sequential-child entry endpoint on the real parent. -/

#def_decl_value parentSeqValue of parentSeq

def parentSeqBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8)]

/-- The sequential parent's elaborated value IS the canonical one-input
instance call on the tagged child, byte for byte. -/
theorem parentSeq_peel : mixedGatePeel parentSeqValue = some (parentSeqBinders,
    instE1 ``childSeq []
      (inputExpr parentSeqBinders.length 0) (inputExpr parentSeqBinders.length 1)) := rfl

/-- **The instance entry contract on the real sequential parent**: under the
run's environment boundaries, the compiled parent/design pair satisfies
`Instance1Preserves` — the parent is the canonical instance body with the
clk/rst connections and freshly added clock ports, over the pinned child. -/
theorem parentSeq_instance_entry {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``parentSeq [] false)
      mctx mref cctx cref w (m, d) w')
    (env : EnvDefines mctx mref cctx cref ``parentSeq parentSeqValue)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment)
      mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e ``childSeq = true)
    (hscalar : ∀ dv : Lean.DefinitionVal, dv.value = parentSeqValue →
      mixedGateResultScalar dv.type = true) :
    Instance1Preserves ``parentSeq parentSeqBinders
      (instE1 ``childSeq []
        (inputExpr parentSeqBinders.length 0) (inputExpr parentSeqBinders.length 1)) m d :=
  instance1_entry_of_env hr env tag
    (fun dv hv => by simp only [certifiedShape?, hv]; rfl)
    hscalar parentSeq_peel rfl rfl

/-! The sequential child's own register-trace endpoint, instantiated. -/

def childSeqTerm : Term (.bits 8) := .bitsInput 8 0

theorem childSeq_wf : childSeqTerm.WF 0 1 (fun _ => 8) := by
  simp [childSeqTerm, Term.WF]

theorem childSeq_library {D : DomainConfig}
    (bi : Nat → Signal D Bool)
    (vi : (j : Nat) → (w : Nat) → Signal D (BitVec w)) :
    Signal.register 0#8 (denote bi vi childSeqTerm) = childSeq (vi 0 8) := rfl

#def_decl_value childSeqValue of childSeq

def childSeqBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`x, .bits 8)]

theorem childSeq_peel : mixedGatePeel childSeqValue = some (childSeqBinders,
    registerE (inputExpr childSeqBinders.length 0) 8 0
      (quote (inputExpr childSeqBinders.length 0)
        (fun _ => inputExpr childSeqBinders.length 0)
        (fun j => inputExpr childSeqBinders.length (j + 1)) childSeqTerm)) := rfl

/-- The register endpoint on the real sequential child: the compiled
child's whole `runModule` trace observes the source register stream. -/
theorem childSeq_run {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    {wst wst' : Void IO.RealWorld} {m : Sparkle.IR.AST.Module}
    {design : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``childSeq [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref ``childSeq childSeqValue) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = childSeqBinders.length ∧
    ∃ (cache : IO.Ref (Lean.ExprStructMap String)) (r : String),
      ∀ {D : DomainConfig} (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat),
      (∀ t stv, SourceInputs ``childSeq childSeqBinders ids cache
          (fun _ => false) (fun i n => (bits i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r = 0 →
      ∃ envs, runModule (Tools.ShippingEntrySoundness.weOf m) m.body seed k st0 mems =
          some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((childSeq (bits 1 8)).val j).toNat := by
  have packaged := Tools.ShippingRegisterSoundness.register_run_of_env (kb := 0) (kv := 1)
    (vw := fun _ => 8) (bpos := fun _ => 0) (vpos := fun j => j + 1) hr env
    (by intro d hd; simp only [certifiedShape?, hd]; rfl) childSeq_peel
    (by simp [childSeqBinders]) childSeq_wf (by decide)
    (by intro j hj; omega)
    (by
      intro j hj
      have h : j = 0 := by omega
      subst h
      exact ⟨`x, rfl⟩)
  obtain ⟨ids, nd, len, cache, r, H⟩ := packaged
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro D bits mems k seed st0 hseed hst0
  apply H (fun _ _ => false) (fun wall i n => (bits i n).val wall)
    mems k seed st0
    (fun j => ((childSeq (bits 1 8)).val j).toNat)
    hseed
  · rw [hst0]
    rfl
  · intro j hj
    rfl

/-- **The sequential parent's linked run observes the source register
stream.** The canonical parent body (as `parentSeq_instance_entry`
derives it and the suite pins it) forwards, cycle by cycle, the pinned
child's certified register trace: the linked `runH` elaboration drives
`out` with `(parentSeq aS).val j` for the whole run. -/
theorem parentSeq_runH_observes {mctxC : Meta.Context}
    {mrefC : ST.Ref IO.RealWorld Meta.State} {cctxC : Core.Context}
    {crefC : ST.Ref IO.RealWorld Core.State} {wC wC' : Void IO.RealWorld}
    {mc m : Sparkle.IR.AST.Module} {designC : Sparkle.IR.AST.Design}
    (hrC : RunsTo (synthesizeCombinationalCore ``childSeq [] false)
      mctxC mrefC cctxC crefC wC (mc, designC) wC')
    (envC : EnvDefines mctxC mrefC cctxC crefC ``childSeq childSeqValue)
    {instName outW aW : String} {we : WEnv}
    (hbody : m.body = instBody mc.name instName
      [("clk", .ref "clk"), ("rst", .ref "rst"), ("_gen_x", .ref aW)] "out" outW)
    (houts : mc.outputs = [⟨"out", .bitVector 8⟩])
    (houtNe : outW ≠ "out") :
    ∃ (ids : List FVarId) (cache : IO.Ref (Lean.ExprStructMap String)) (r : String),
      ids.Nodup ∧ ids.length = childSeqBinders.length ∧
      ∀ {D : DomainConfig} (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
        (mems : MEnv) (k : Nat) (seedP : Nat → Env) (st0 : String → Nat),
      (∀ t stv, SourceInputs ``childSeq childSeqBinders ids cache
          (fun _ => false) (fun i n => (bits i n).val (k - 1 - t))
          (connEnvS ([("clk", .ref "clk"), ("rst", .ref "rst"),
            ("_gen_x", .ref aW)] ++ [("out", .ref outW)]) (seedP t) stv) ∧
        connEnvS ([("clk", .ref "clk"), ("rst", .ref "rst"),
            ("_gen_x", .ref aW)] ++ [("out", .ref outW)]) (seedP t) stv "rst" = 0 ∧
        connEnvS ([("clk", .ref "clk"), ("rst", .ref "rst"),
            ("_gen_x", .ref aW)] ++ [("out", .ref outW)]) (seedP t) stv r = stv r) →
      st0 r = 0 →
      ∃ envsP, runH we
          (fun n => if n = mc.name then
            some (mc, Tools.ShippingEntrySoundness.weOf mc) else none)
          m.body seedP k st0 mems = some envsP ∧
        envsP.length = k ∧
        ∀ j (hj : j < envsP.length),
          (envsP[j]'hj) "out" = ((parentSeq (bits 1 8)).val j).toNat := by
  obtain ⟨ids, nd, len, cache, r, HC⟩ := childSeq_run hrC envC
  refine ⟨ids, cache, r, nd, len, ?_⟩
  intro D bits mems k seedP st0 hseed hst0
  obtain ⟨envsC, hrunC, hlenC, hobsC⟩ := HC bits mems k
    (fun t stv => connEnvS ([("clk", .ref "clk"), ("rst", .ref "rst"),
      ("_gen_x", .ref aW)] ++ [("out", .ref outW)]) (seedP t) stv) st0 hseed hst0
  obtain ⟨envsP, hrunP, hlenP, hfwd⟩ := instBody_runH (we := we)
    (children := fun n => if n = mc.name then
      some (mc, Tools.ShippingEntrySoundness.weOf mc) else none)
    (mn := mc.name) (instName := instName)
    (inConns := [("clk", .ref "clk"), ("rst", .ref "rst"), ("_gen_x", .ref aW)])
    (childOut := "out") (outW := outW)
    (by simp) houts
    (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · rcases List.mem_cons.mp hp with rfl | hp
        · rfl
        · rcases List.mem_cons.mp hp with rfl | hp
          · rfl
          · cases hp) houtNe
    k st0 mems envsC hrunC
  refine ⟨envsP, by rw [hbody]; exact hrunP, by rw [hlenP, hlenC], ?_⟩
  intro j hj
  rw [hfwd j hj (by rw [← hlenP]; exact hj)]
  exact hobsC j (by rw [← hlenP]; exact hj)

/-! The n-ary instance entry endpoint, on a real three-input parent. -/

#def_decl_value parentUse3Value of parentUse3

def parentUse3Binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8), (`c, .bits 8)]

theorem parentUse3_peel : mixedGatePeel parentUse3Value = some (parentUse3Binders,
    instEN ``childAdd3 [] (inputExpr parentUse3Binders.length 0)
      ([1, 2, 3].map (inputExpr parentUse3Binders.length))) := rfl

/-- **The n-ary instance entry contract on a real three-input parent**:
the general-arity monolith, instantiated — the compiled parent is one
instance statement over the port-ordered connection list plus the output
alias, over the pinned child. -/
theorem parentUse3_instance_entry {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``parentUse3 [] false)
      mctx mref cctx cref w (m, d) w')
    (env : EnvDefines mctx mref cctx cref ``parentUse3 parentUse3Value)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment)
      mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e ``childAdd3 = true)
    (hscalar : ∀ dv : Lean.DefinitionVal, dv.value = parentUse3Value →
      mixedGateResultScalar dv.type = true) :
    InstanceNPreserves ``parentUse3 parentUse3Binders
      (instEN ``childAdd3 [] (inputExpr parentUse3Binders.length 0)
        ([1, 2, 3].map (inputExpr parentUse3Binders.length))) m d :=
  instanceN_entry_of_env hr env tag
    (fun dv hv => by simp only [certifiedShape?, hv]; rfl)
    hscalar parentUse3_peel ⟨_, _, rfl⟩
    (fun q hq => by
      simp at hq
      rcases hq with rfl | rfl | rfl <;> exact ⟨_, _, rfl⟩)

/-! The GENERAL single-output entry endpoint, on a real two-data-port
sequential parent. -/

#def_decl_value parentSeq2Value of parentSeq2

def parentSeq2Binders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]

theorem parentSeq2_peel : mixedGatePeel parentSeq2Value = some (parentSeq2Binders,
    instEN ``childSeq2 [] (inputExpr parentSeq2Binders.length 0)
      ([1, 2].map (inputExpr parentSeq2Binders.length))) := rfl

/-- **The general instance entry contract on a real sequential parent with
two data ports**: one instance statement — clk/rst connected to same-named
parent ports, the data ports to the prepared argument wires in order — over
the pinned child, from the real compile under the run boundaries. -/
theorem parentSeq2_instance_entry {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``parentSeq2 [] false)
      mctx mref cctx cref w (m, d) w')
    (env : EnvDefines mctx mref cctx cref ``parentSeq2 parentSeq2Value)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment)
      mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e ``childSeq2 = true)
    (hscalar : ∀ dv : Lean.DefinitionVal, dv.value = parentSeq2Value →
      mixedGateResultScalar dv.type = true) :
    InstanceGPreserves ``parentSeq2 parentSeq2Binders
      (instEN ``childSeq2 [] (inputExpr parentSeq2Binders.length 0)
        ([1, 2].map (inputExpr parentSeq2Binders.length))) m d :=
  instanceG_entry_of_env hr env tag
    (fun dv hv => by simp only [certifiedShape?, hv]; rfl)
    hscalar parentSeq2_peel ⟨_, _, rfl⟩
    (fun q hq => by
      simp at hq
      rcases hq with rfl | rfl <;> exact ⟨_, _, rfl⟩)

/-! The projection entry endpoint, on a real parent selecting the SECOND
field of a two-output child. -/

/-- The multi-output child module the pipeline emits, pinned literally. -/
def childTwoModule : Sparkle.IR.AST.Module :=
  { name := "Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest.childTwo"
    inputs := [⟨"_gen_x", .bitVector 8⟩, ⟨"_gen_y", .bitVector 8⟩]
    outputs := [⟨"lo", .bitVector 8⟩, ⟨"hi", .bitVector 8⟩]
    wires := [⟨"_gen_x", .bitVector 8⟩, ⟨"_gen_y", .bitVector 8⟩,
      ⟨"_gen_lo", .bitVector 8⟩, ⟨"_gen_hi", .bitVector 8⟩]
    body := [.assign "_gen_lo" (.op .add [.ref "_gen_x", .ref "_gen_y"]),
      .assign "lo" (.ref "_gen_lo"),
      .assign "_gen_hi" (.op .sub [.ref "_gen_x", .ref "_gen_y"]),
      .assign "hi" (.ref "_gen_hi")]
    parameters := [] }

def childTwoWe : WEnv := fun n =>
  if n == "_gen_x" || n == "_gen_y" || n == "_gen_lo" || n == "_gen_hi" ||
    n == "lo" || n == "hi" then 8 else 0

def childrenTwo : String → Option (Sparkle.IR.AST.Module × WEnv) :=
  fun n => if n = childTwoModule.name then some (childTwoModule, childTwoWe) else none

#def_decl_value parentHiValue of parentHi

def parentHiBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]

theorem parentHi_peel : mixedGatePeel parentHiValue = some (parentHiBinders,
    projE ``TwoOut.hi [] (inputExpr parentHiBinders.length 0)
      (instEN ``childTwo [] (inputExpr parentHiBinders.length 0)
        ([1, 2].map (inputExpr parentHiBinders.length)))) := rfl

/-- **The projection instance entry contract on a real parent**: one instance
statement connecting EVERY output port of the two-output child to its own
fresh wire, plus the alias reading the projected field's wire — from the
real compile under the run boundaries. -/
theorem parentHi_instance_entry {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``parentHi [] false)
      mctx mref cctx cref w (m, d) w')
    (env : EnvDefines mctx mref cctx cref ``parentHi parentHiValue)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment)
      mctx mref cctx cref wE e wE' →
      (∃ sn, e.getProjectionStructureName? ``TwoOut.hi = some sn) ∧
      Sparkle.Compiler.isHardwareModule e ``childTwo = true)
    (hscalar : ∀ dv : Lean.DefinitionVal, dv.value = parentHiValue →
      mixedGateResultScalar dv.type = true) :
    ProjInstancePreserves ``parentHi parentHiBinders
      (projE ``TwoOut.hi [] (inputExpr parentHiBinders.length 0)
        (instEN ``childTwo [] (inputExpr parentHiBinders.length 0)
          ([1, 2].map (inputExpr parentHiBinders.length)))) m d :=
  instanceProj_entry_of_env hr env tag
    (fun dv hv => by simp only [certifiedShape?, hv]; rfl)
    hscalar parentHi_peel ⟨_, _, rfl⟩ ⟨_, _, rfl⟩
    (fun q hq => by
      simp at hq
      rcases hq with rfl | rfl <;> exact ⟨_, _, rfl⟩)

/-- **The projected entry output observes the source field.** The compiled
parent's body, elaborated with the two-output child bound to its pinned
compile, drives `out` with `(parentHi aS bS).val t` — the SECOND field of
the source record — whenever the prepared argument ports carry `aS.val t`
and `bS.val t`. -/
theorem parentHi_entry_observes {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``parentHi [] false)
      mctx mref cctx cref w (m, d) w')
    (env : EnvDefines mctx mref cctx cref ``parentHi parentHiValue)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment)
      mctx mref cctx cref wE e wE' →
      (∃ sn, e.getProjectionStructureName? ``TwoOut.hi = some sn) ∧
      Sparkle.Compiler.isHardwareModule e ``childTwo = true)
    (hscalar : ∀ dv : Lean.DefinitionVal, dv.value = parentHiValue →
      mixedGateResultScalar dv.type = true)
    {dc : Sparkle.IR.AST.Design}
    (hpenv : ProjEnvDefines ``TwoOut.hi ``TwoOut ``childTwo)
    (hfield : ProjFieldDefines ``TwoOut.hi ``TwoOut "hi")
    (hsub : SubSynthDefines ``childTwo childTwoModule dc)
    (hcache : OutCacheEmpty)
    (hdc : dc.modules = []) :
    ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) {D : DomainConfig}
      (aS bS : Signal D (BitVec 8)) (t : Nat) (mems : MEnv) (we : WEnv),
    let a := Tools.ShippingMixedEntrySoundness.start
      (entryCompilerState false cache) (``parentHi).toString
    let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
      (parentHiBinders.zip [i0, i1, i2]) a
    Tools.ShippingMixedEntrySoundness.Admissible bools bits env0
      (parentHiBinders.zip [i0, i1, i2]) a →
    p.bits i1 = some ⟨8, aS.val t⟩ → p.bits i2 = some ⟨8, bS.val t⟩ →
    d.modules = [childTwoModule] ∧
    ∃ envF, evalAssignsH we childrenTwo mems m.body env0 = some envF ∧
      envF "out" = ((parentHi aS bS).val t).toNat := by
  obtain ⟨ids, nd, len, cache, P⟩ := parentHi_instance_entry hr env tag hscalar
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  obtain ⟨instName, outW, oWs, conns, hlenO, hndO, hlook, R⟩ :=
    P ``TwoOut.hi ``TwoOut [] i0 "hi" ``childTwo [] i0 [i1, i2] childTwoModule dc
      childTwoModule.inputs childTwoModule.outputs
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      hpenv hfield hsub hcache hdc rfl rfl (by decide) rfl rfl
  have lenO2 : oWs.length = 2 := hlenO
  rcases oWs with _ | ⟨o0, oWs⟩
  · cases lenO2
  rcases oWs with _ | ⟨o1, oWs⟩
  · cases lenO2
  rcases oWs with _ | ⟨o2, oWs⟩
  rotate_left
  · simp at lenO2
  have hoW : outW = o1 := by
    have : (some o1 : Option String) = some outW := hlook
    exact (Option.some.inj this).symm
  have hne : o0 ≠ o1 := by
    intro eq
    rw [eq] at hndO
    simp at hndO
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro bools bits env0 D aS bS t mems we a p adm ha0 hb0
  obtain ⟨hbody, hdmods, houtNe, -, -, aWs, hlenW, hconns, hvals⟩ :=
    R bools bits env0 (fun _ => 8)
      (fun i => if i = 0 then aS.val t else bS.val t) adm
      (fun i hi => by
        rcases i with _ | i
        · exact ha0
        · rcases i with _ | i
          · exact hb0
          · exact absurd hi (by simp))
  have lenW2 : aWs.length = 2 := hlenW
  rcases aWs with _ | ⟨aW, aWs⟩
  · cases lenW2
  rcases aWs with _ | ⟨bW, aWs⟩
  · cases lenW2
  rcases aWs with _ | ⟨cW, aWs⟩
  rotate_left
  · simp at lenW2
  have hconns' : conns.reverse =
      [("_gen_x", Sparkle.IR.AST.Expr.ref aW), ("_gen_y", Sparkle.IR.AST.Expr.ref bW)] :=
    hconns
  have haV : env0 aW = (aS.val t).toNat := (hvals 0 (Nat.zero_lt_succ _)).1
  have hbV : env0 bW = (bS.val t).toNat := (hvals 1 (Nat.lt_succ_self _)).1
  refine ⟨by rw [hdmods], ?_⟩
  have hrun : evalAssigns childTwoWe mems childTwoModule.body
      (connEnv [("_gen_x", Sparkle.IR.AST.Expr.ref aW),
        ("_gen_y", Sparkle.IR.AST.Expr.ref bW),
        ("lo", Sparkle.IR.AST.Expr.ref o0),
        ("hi", Sparkle.IR.AST.Expr.ref o1)] env0) =
      some (fun n =>
        if n = "hi" then mask 8 (env0 aW + (2 ^ 8 - mask 8 (env0 bW)))
        else if n = "_gen_hi" then mask 8 (env0 aW + (2 ^ 8 - mask 8 (env0 bW)))
        else if n = "lo" then mask 8 (env0 aW + env0 bW)
        else if n = "_gen_lo" then mask 8 (env0 aW + env0 bW)
        else connEnv [("_gen_x", Sparkle.IR.AST.Expr.ref aW),
          ("_gen_y", Sparkle.IR.AST.Expr.ref bW),
          ("lo", Sparkle.IR.AST.Expr.ref o0),
          ("hi", Sparkle.IR.AST.Expr.ref o1)] env0 n) := rfl
  obtain ⟨envF, hev, hout⟩ := instAlias_linked (we := we) (mems := mems)
    (children := childrenTwo) (mn := childTwoModule.name) (instName := instName)
    (outW := o1) rfl hrun
  refine ⟨envF, ?_, ?_⟩
  · rw [hbody, hconns', hoW]
    exact hev
  · rw [hout]
    show (if o1 = o1 then mask 8 (env0 aW + (2 ^ 8 - mask 8 (env0 bW)))
      else if o1 = o0 then mask 8 (env0 aW + env0 bW) else env0 o1) = _
    rw [if_pos rfl, haV, hbV]
    show ((aS.val t).toNat + (2 ^ 8 - (bS.val t).toNat % 2 ^ 8)) % 2 ^ 8 =
      ((aS.val t - bS.val t)).toNat
    rw [BitVec.toNat_sub, Nat.mod_eq_of_lt (bS.val t).isLt]
    omega

/-- **The entry output observes the source composition.** Combining the
instance contract of THIS compile with the linked-instance semantics: the
compiled parent's body, elaborated with the child bound to its pinned
compile, drives `out` with `(parentUse aS bS).val t` — the source value —
whenever the prepared argument ports carry `aS.val t` and `bS.val t`. The
run boundaries (`EnvDefines`, the tag, the child pin, the empty cache and
the scalar result type) are the retained premises. -/
theorem parentUse_entry_observes {mctx : Meta.Context}
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
      mixedGateResultScalar dv.type = true)
    {dc : Sparkle.IR.AST.Design}
    (htagAll : HardwareTagged ``childAdd)
    (hsub : SubSynthDefines ``childAdd childModule dc)
    (hdc : dc.modules = []) :
    ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String))
      (instName outW aW bW : String),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) {D : DomainConfig}
      (aS bS : Signal D (BitVec 8)) (t : Nat) (mems : MEnv) (we : WEnv),
    let a := Tools.ShippingMixedEntrySoundness.start
      (entryCompilerState false cache) (``parentUse).toString
    let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
      (parentUseBinders.zip [i0, i1, i2]) a
    Tools.ShippingMixedEntrySoundness.Admissible bools bits env0
      (parentUseBinders.zip [i0, i1, i2]) a →
    p.bits i1 = some ⟨8, aS.val t⟩ → p.bits i2 = some ⟨8, bS.val t⟩ →
    d.modules = [childModule] ∧
    ∃ envF, evalAssignsH we (childrenOf childModule.name) mems m.body env0 = some envF ∧
      envF "out" = ((parentUse aS bS).val t).toNat := by
  obtain ⟨ids, nd, len, cache, P⟩ := parentUse_instance_entry hr env tag hscalar
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  obtain ⟨instName, outW, aW, bW, R⟩ :=
    P ``childAdd [] i0 i1 i2 childModule dc 8 8 8 "_gen_x" "_gen_y"
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      htagAll hsub hdc rfl rfl rfl rfl rfl rfl
  refine ⟨i0, i1, i2, cache, instName, outW, aW, bW, ?_⟩
  intro bools bits env0 D aS bS t mems we a p adm ha0 hb0
  obtain ⟨hbody, hdmods, houtNe, haNe, hbNe, haV, hbV⟩ :=
    R bools bits env0 (aS.val t) (bS.val t) adm ha0 hb0
  refine ⟨by rw [hdmods], ?_⟩
  -- the child's evaluation on the connection-fed environment, computed
  have hrun : evalAssigns childWe mems childModule.body
      (connEnv [("_gen_x", Sparkle.IR.AST.Expr.ref aW),
        ("_gen_y", Sparkle.IR.AST.Expr.ref bW),
        ("out", Sparkle.IR.AST.Expr.ref outW)] env0) =
      some (fun n =>
        if n = "out" then mask 8 (env0 aW + env0 bW)
        else if n = "_gen_out" then mask 8 (env0 aW + env0 bW)
        else connEnv [("_gen_x", Sparkle.IR.AST.Expr.ref aW),
          ("_gen_y", Sparkle.IR.AST.Expr.ref bW),
          ("out", Sparkle.IR.AST.Expr.ref outW)] env0 n) := rfl
  obtain ⟨envF, hev, hout, -⟩ := instBody_linked (we := we) (mems := mems)
    (children := childrenOf childModule.name)
    (mn := childModule.name) (instName := instName)
    (inConns := [("_gen_x", .ref aW), ("_gen_y", .ref bW)])
    (childOut := "out") (outW := outW)
    rfl rfl (fun p hp => by
      rcases List.mem_cons.mp hp with rfl | hp
      · rfl
      · rcases List.mem_cons.mp hp with rfl | hp
        · rfl
        · cases hp) hrun houtNe
  refine ⟨envF, ?_, ?_⟩
  · rw [hbody]
    exact hev
  · rw [hout]
    show mask 8 (env0 aW + env0 bW) = _
    rw [haV, hbV]
    show (((aS.val t).toNat) + ((bS.val t).toNat)) % 2 ^ 8 =
      ((aS.val t + bS.val t)).toNat
    rw [BitVec.toNat_add]

/-! Cones over instance leaves: the parent computes on the child's result. -/

#def_decl_value parentMixValue of parentMix

def parentMixBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]

/-- The cone's BitVec leaves: leaf 0 is the instance call, leaf 1 the input `a`. -/
def parentMixLeaf (dom : Lean.Expr) (a b : Lean.Expr) (j : Nat) : Lean.Expr :=
  if j = 0 then instEN ``childAdd [] dom [a, b] else a

def parentMixTerm : Term (.bits 8) := .binary .add (.bitsInput 8 0) (.bitsInput 8 1)

theorem parentMix_wf : parentMixTerm.WF 0 2 (fun _ => 8) :=
  ⟨⟨by decide, rfl, by decide⟩, ⟨by decide, rfl, by decide⟩⟩

theorem parentMix_peel : mixedGatePeel parentMixValue = some (parentMixBinders,
    quote (inputExpr parentMixBinders.length 0)
      (fun _ => inputExpr parentMixBinders.length 0)
      (parentMixLeaf (inputExpr parentMixBinders.length 0)
        (inputExpr parentMixBinders.length 1) (inputExpr parentMixBinders.length 2))
      parentMixTerm) := rfl

/-- The linked child's source function: `childAdd` on two 8-bit values. -/
def addSem : ChildSem where
  childSem mn vs :=
    if mn = ``childAdd ∧ vs.map Value.kind = [.bits 8, .bits 8] then
      some (.bits 8 (BitVec.ofNat 8 ((vs.map Value.toNat).sum)))
    else none

/-- The pinned child module computes its source function. -/
theorem childAdd_correct :
    @ChildCorrect addSem ``childAdd childModule childWe "out" := by
  intro mems envIn vs v hsem hports
  have hsem' : (if ``childAdd = ``childAdd ∧ vs.map Value.kind = [.bits 8, .bits 8] then
      some (Value.bits 8 (BitVec.ofNat 8 ((vs.map Value.toNat).sum))) else none) = some v := hsem
  split at hsem'
  · rename_i hc
    cases hsem'
    have hl : vs.length = 2 := by
      have := congrArg List.length hc.2
      simpa using this
    rcases vs with _ | ⟨v1, vs⟩
    · cases hl
    rcases vs with _ | ⟨v2, vs⟩
    · cases hl
    rcases vs with _ | ⟨v3, vs⟩
    rotate_left
    · simp at hl
    have h0 : envIn "_gen_x" = v1.toNat := hports 0 (by decide) (Nat.zero_lt_succ _)
    have h1 : envIn "_gen_y" = v2.toNat := hports 1 (by decide) (Nat.lt_succ_self _)
    refine ⟨fun n =>
      if n = "out" then mask 8 (envIn "_gen_x" + envIn "_gen_y")
      else if n = "_gen_out" then mask 8 (envIn "_gen_x" + envIn "_gen_y")
      else envIn n, rfl, ?_⟩
    show mask 8 (envIn "_gen_x" + envIn "_gen_y") =
      (BitVec.ofNat 8 (v1.toNat + (v2.toNat + 0))).toNat
    rw [h0, h1]
    simp [mask, BitVec.toNat_ofNat]
  · cases hsem'

/-- **A cone over an instance leaf observes its source.** The parent
`childAdd a b + a` compiles through the certified front end; the compiled
module's LINKED evaluation — the instance statement executed against the
pinned child — drives `out` with `(parentMix aS bS).val t`. The child is
an instance LEAF of the cone, lowered through the leaf contract; the
retained premises are the run boundaries. -/
theorem parentMix_entry_observes {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``parentMix [] false)
      mctx mref cctx cref w (m, d) w')
    (env : EnvDefines mctx mref cctx cref ``parentMix parentMixValue)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment)
      mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e ``childAdd = true)
    (hscalar : ∀ dv : Lean.DefinitionVal, dv.value = parentMixValue →
      mixedGateResultScalar dv.type = true)
    {dc : Sparkle.IR.AST.Design}
    (htagAll : HardwareTagged ``childAdd)
    (hsub : SubSynthDefinesAll ``childAdd childModule dc)
    (hdc : dc.modules = []) :
    ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) {D : DomainConfig}
      (aS bS : Signal D (BitVec 8)) (t : Nat) (mems : MEnv),
    let a := Tools.ShippingMixedEntrySoundness.start
      (entryCompilerState false cache) (``parentMix).toString
    let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
      (parentMixBinders.zip [i0, i1, i2]) a
    Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
      (parentMixBinders.zip [i0, i1, i2]) a →
    p.bits i1 = some ⟨8, aS.val t⟩ → p.bits i2 = some ⟨8, bS.val t⟩ →
    (∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths m)
        (childrenOf childModule.name) mems m.body initial = some result ∧
      result "out" = ((parentMix aS bS).val t).toNat) ∧
    InstsLinked (childrenOf childModule.name) m := by
  have H := hierCone_entry_of_env hr env
    (fun dv hv => by simp only [certifiedShape?, hv]; rfl)
    hscalar parentMix_peel parentMix_wf rfl
    (fun wE envR wE' henv => by
      refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), ?_⟩
      intro j hj
      have ht := instancePredicate_instEN envR ``childAdd []
        (inputExpr parentMixBinders.length 0)
        ([1, 2].map (inputExpr parentMixBinders.length)) (tag _ _ _ henv)
      rcases j with _ | j
      · show (instancePredicate envR (instEN ``childAdd []
            (inputExpr parentMixBinders.length 0)
            ([1, 2].map (inputExpr parentMixBinders.length))) && true && true) = true
        rw [ht]
        rfl
      · rcases j with _ | j
        · rfl
        · exact absurd hj (by simp))
  obtain ⟨ids, nd, len, cache, P⟩ := H
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro bools bits initial D aS bS t mems a p adm ha0 hb0
  obtain ⟨separate, Q⟩ := P (childrenOf childModule.name) addSem bools bits initial mems adm
  have hA : inputValues p.bools p.bits i1 = some (.bits 8 (aS.val t)) :=
    inputValues_bits separate ha0
  have hB : inputValues p.bools p.bits i2 = some (.bits 8 (bS.val t)) :=
    inputValues_bits separate hb0
  letI : HierCtx := hierLink (childrenOf childModule.name)
  letI : ChildSem := addSem
  -- the instance leaf: its meaning and its contract
  have hargsM : ∀ k (hk : k < [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length)
      (hk' : k < [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)].length),
      Meaning (inputValues p.bools p.bits)
        ([Lean.Expr.fvar i1, Lean.Expr.fvar i2][k]'hk)
        ([Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)][k]'hk') := by
    intro k hk hk'
    rcases k with _ | k
    · exact .input rfl hA
    · rcases k with _ | k
      · exact .input rfl hB
      · exact absurd hk (by simp)
  have hsem : ChildSem.childSem ``childAdd
      [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)] =
      some (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) := by
    show (if ``childAdd = ``childAdd ∧
        [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)].map Value.kind =
          [.bits 8, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  have leafM : LeafMeaning addSem (inputValues p.bools p.bits)
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) :=
    meaning_inst rfl rfl hargsM hsem
  have leafC : LeafContract (childrenOf childModule.name) addSem p.context
      (inputValues p.bools p.bits) mems initial
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat))) := by
    intro we fuel
    exact inst_leaf_fuel (mc := childModule) (dc := dc) (cwe := childWe)
      (outName := "out") (wOut := 8)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      htagAll hsub hdc (by decide) (by decide) rfl (by decide) rfl rfl hargsM
      (fun k hk hk' fuel => by
        rcases k with _ | k
        · exact input_contract_fuel hA fuel
        · rcases k with _ | k
          · exact input_contract_fuel hB fuel
          · exact absurd hk (by simp))
      hsem rfl rfl childAdd_correct fuel
  have value := Q (.fvar i0) 0 2 (fun _ => 8) (fun _ => .fvar i0)
    (parentMixLeaf (.fvar i0) (.fvar i1) (.fvar i2)) (fun _ => false)
    (fun j w => if j = 0 then BitVec.ofNat w ((aS.val t).toNat + (bS.val t).toNat)
      else BitVec.ofNat w (aS.val t).toNat)
    parentMixTerm parentMix_wf
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact leafM
      · rcases j with _ | j
        · show Meaning (inputValues p.bools p.bits) (.fvar i1)
            (.bits 8 (BitVec.ofNat 8 (aS.val t).toNat))
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
          exact .input rfl hA
        · exact absurd hj (by simp))
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      rcases j with _ | j
      · exact leafC
      · rcases j with _ | j
        · intro we fuel
          show Contract (translateFuelFix translateStep fuel) p.context
            (inputValues p.bools p.bits) we mems initial (.fvar i1)
            (.bits 8 (BitVec.ofNat 8 (aS.val t).toNat))
          rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
          exact input_contract_fuel hA fuel
        · exact absurd hj (by simp))
    rfl
  obtain ⟨⟨result, hev, hout⟩, linked⟩ := value
  refine ⟨⟨result, hev, ?_⟩, linked⟩
  rw [hout]
  show (BitVec.ofNat 8 ((aS.val t).toNat + (bS.val t).toNat) +
    BitVec.ofNat 8 (aS.val t).toNat).toNat = ((aS.val t + bS.val t) + aS.val t).toNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rfl

/-! A module PIPELINE: an instance call whose operand is an instance call. -/

#def_decl_value parentNestedValue of parentNested

def parentNestedBinders : List (Name × MixedGateBinder) :=
  [(`dom, .domain), (`a, .bits 8), (`b, .bits 8)]

/-- `childAdd (childAdd a b) b`, quoted. -/
def nestedE (dom a b : Lean.Expr) : Lean.Expr :=
  instEN ``childAdd [] dom [instEN ``childAdd [] dom [a, b], b]

theorem parentNested_peel : mixedGatePeel parentNestedValue = some (parentNestedBinders,
    nestedE (inputExpr parentNestedBinders.length 0) (inputExpr parentNestedBinders.length 1)
      (inputExpr parentNestedBinders.length 2)) := rfl

/-- **A module pipeline observes its source.** The parent
`childAdd (childAdd a b) b` compiles through the certified front end to two
instance statements; the linked evaluation drives `out` with
`(parentNested aS bS).val t`. The outer call's leaf contract consumes the
inner call's leaf contract as an operand contract. -/
theorem parentNested_entry_observes {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Sparkle.IR.AST.Design}
    (hr : RunsTo (synthesizeCombinationalCore ``parentNested [] false)
      mctx mref cctx cref w (m, d) w')
    (env : EnvDefines mctx mref cctx cref ``parentNested parentNestedValue)
    (tag : ∀ wE e wE', RunsTo (Lean.getEnv : MetaM Environment)
      mctx mref cctx cref wE e wE' →
      Sparkle.Compiler.isHardwareModule e ``childAdd = true)
    (hscalar : ∀ dv : Lean.DefinitionVal, dv.value = parentNestedValue →
      mixedGateResultScalar dv.type = true)
    {dc : Sparkle.IR.AST.Design}
    (htagAll : HardwareTagged ``childAdd)
    (hsub : SubSynthDefinesAll ``childAdd childModule dc)
    (hdc : dc.modules = []) :
    ∃ (i0 i1 i2 : FVarId) (cache : IO.Ref (Lean.ExprStructMap String)),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (initial : Env) {D : DomainConfig}
      (aS bS : Signal D (BitVec 8)) (t : Nat) (mems : MEnv),
    let a := Tools.ShippingMixedEntrySoundness.start
      (entryCompilerState false cache) (``parentNested).toString
    let p := Tools.ShippingMixedEntrySoundness.prepare bools bits
      (parentNestedBinders.zip [i0, i1, i2]) a
    Tools.ShippingMixedEntrySoundness.Admissible bools bits initial
      (parentNestedBinders.zip [i0, i1, i2]) a →
    p.bits i1 = some ⟨8, aS.val t⟩ → p.bits i2 = some ⟨8, bS.val t⟩ →
    ∃ result, evalAssignsH (Tools.ShippingMixedEntrySoundness.moduleWidths m)
        (childrenOf childModule.name) mems m.body initial = some result ∧
      result "out" = ((parentNested aS bS).val t).toNat := by
  have H := hierRoot_entry_of_env hr env
    (fun dv hv => by simp only [certifiedShape?, hv]; rfl)
    hscalar parentNested_peel
    (fun wE envR wE' henv => by
      have hto := instancePredicate_instEN envR ``childAdd []
        (inputExpr parentNestedBinders.length 0)
        [instEN ``childAdd [] (inputExpr parentNestedBinders.length 0)
          [inputExpr parentNestedBinders.length 1, inputExpr parentNestedBinders.length 2],
         inputExpr parentNestedBinders.length 2] (tag _ _ _ henv)
      have hti := instancePredicate_instEN envR ``childAdd []
        (inputExpr parentNestedBinders.length 0)
        [inputExpr parentNestedBinders.length 1, inputExpr parentNestedBinders.length 2]
        (tag _ _ _ henv)
      show (instancePredicate envR (instEN ``childAdd []
          (inputExpr parentNestedBinders.length 0)
          [instEN ``childAdd [] (inputExpr parentNestedBinders.length 0)
            [inputExpr parentNestedBinders.length 1,
             inputExpr parentNestedBinders.length 2],
           inputExpr parentNestedBinders.length 2]) && true &&
        (true && (instancePredicate envR (instEN ``childAdd []
          (inputExpr parentNestedBinders.length 0)
          [inputExpr parentNestedBinders.length 1,
           inputExpr parentNestedBinders.length 2]) && true && true && true))) = true
      rw [hto, hti]
      rfl)
  obtain ⟨ids, nd, len, cache, P⟩ := H
  have len3 : ids.length = 3 := len
  rcases ids with _ | ⟨i0, ids⟩
  · cases len3
  rcases ids with _ | ⟨i1, ids⟩
  · cases len3
  rcases ids with _ | ⟨i2, ids⟩
  · cases len3
  rcases ids with _ | ⟨i3, ids⟩
  rotate_left
  · simp at len3
  refine ⟨i0, i1, i2, cache, ?_⟩
  intro bools bits initial D aS bS t mems a p adm ha0 hb0
  obtain ⟨separate, Q⟩ := P (childrenOf childModule.name) addSem bools bits initial mems adm
  have hA : inputValues p.bools p.bits i1 = some (.bits 8 (aS.val t)) :=
    inputValues_bits separate ha0
  have hB : inputValues p.bools p.bits i2 = some (.bits 8 (bS.val t)) :=
    inputValues_bits separate hb0
  letI : HierCtx := hierLink (childrenOf childModule.name)
  letI : ChildSem := addSem
  -- the inner call
  have innerArgsM : ∀ k (hk : k < [Lean.Expr.fvar i1, Lean.Expr.fvar i2].length)
      (hk' : k < [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)].length),
      Meaning (inputValues p.bools p.bits)
        ([Lean.Expr.fvar i1, Lean.Expr.fvar i2][k]'hk)
        ([Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)][k]'hk') := by
    intro k hk hk'
    rcases k with _ | k
    · exact .input rfl hA
    · rcases k with _ | k
      · exact .input rfl hB
      · exact absurd hk (by simp)
  have innerSem : ChildSem.childSem ``childAdd
      [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)] =
      some (.bits 8 (aS.val t + bS.val t)) := by
    show (if ``childAdd = ``childAdd ∧
        [Value.bits 8 (aS.val t), Value.bits 8 (bS.val t)].map Value.kind =
          [.bits 8, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  have innerM : Meaning (inputValues p.bools p.bits)
      (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
      (.bits 8 (aS.val t + bS.val t)) :=
    meaning_inst rfl rfl innerArgsM innerSem
  have innerC : ∀ (we : WEnv) (fuel : Nat),
      Contract (translateFuelFix translateStep fuel) p.context
        (inputValues p.bools p.bits) we mems initial
        (instEN ``childAdd [] (.fvar i0) [.fvar i1, .fvar i2])
        (.bits 8 (aS.val t + bS.val t)) := by
    intro we fuel
    exact inst_leaf_fuel (mc := childModule) (dc := dc) (cwe := childWe)
      (outName := "out") (wOut := 8)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      htagAll hsub hdc (by decide) (by decide) rfl (by decide) rfl rfl innerArgsM
      (fun k hk hk' fuel => by
        rcases k with _ | k
        · exact input_contract_fuel hA fuel
        · rcases k with _ | k
          · exact input_contract_fuel hB fuel
          · exact absurd hk (by simp))
      innerSem rfl rfl childAdd_correct fuel
  -- the outer call: its first operand is the inner call
  have outerArgsM : ∀ k
      (hk : k < [instEN ``childAdd [] (Lean.Expr.fvar i0)
        [Lean.Expr.fvar i1, Lean.Expr.fvar i2], Lean.Expr.fvar i2].length)
      (hk' : k < [Value.bits 8 (aS.val t + bS.val t), Value.bits 8 (bS.val t)].length),
      Meaning (inputValues p.bools p.bits)
        ([instEN ``childAdd [] (Lean.Expr.fvar i0)
          [Lean.Expr.fvar i1, Lean.Expr.fvar i2], Lean.Expr.fvar i2][k]'hk)
        ([Value.bits 8 (aS.val t + bS.val t), Value.bits 8 (bS.val t)][k]'hk') := by
    intro k hk hk'
    rcases k with _ | k
    · exact innerM
    · rcases k with _ | k
      · exact .input rfl hB
      · exact absurd hk (by simp)
  have outerSem : ChildSem.childSem ``childAdd
      [Value.bits 8 (aS.val t + bS.val t), Value.bits 8 (bS.val t)] =
      some (.bits 8 (aS.val t + bS.val t + bS.val t)) := by
    show (if ``childAdd = ``childAdd ∧
        [Value.bits 8 (aS.val t + bS.val t), Value.bits 8 (bS.val t)].map Value.kind =
          [.bits 8, .bits 8] then _ else none) = _
    rw [if_pos ⟨rfl, rfl⟩]
    rfl
  have leafM : LeafMeaning addSem (inputValues p.bools p.bits)
      (nestedE (.fvar i0) (.fvar i1) (.fvar i2))
      (.bits 8 (aS.val t + bS.val t + bS.val t)) :=
    meaning_inst rfl rfl outerArgsM outerSem
  have leafC : LeafContract (childrenOf childModule.name) addSem p.context
      (inputValues p.bools p.bits) mems initial
      (nestedE (.fvar i0) (.fvar i1) (.fvar i2))
      (.bits 8 (aS.val t + bS.val t + bS.val t)) := by
    intro we fuel
    exact inst_leaf_fuel (mc := childModule) (dc := dc) (cwe := childWe)
      (outName := "out") (wOut := 8)
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
      htagAll hsub hdc (by decide) (by decide) rfl (by decide) rfl rfl outerArgsM
      (fun k hk hk' fuel => by
        rcases k with _ | k
        · exact innerC we fuel
        · rcases k with _ | k
          · exact input_contract_fuel hB fuel
          · exact absurd hk (by simp))
      outerSem rfl rfl childAdd_correct fuel
  have value := Q (.fvar i0) 0 1 (fun _ => 8) (fun _ => .fvar i0)
    (fun _ => nestedE (.fvar i0) (.fvar i1) (.fvar i2)) (fun _ => false)
    (fun _ w => BitVec.ofNat w (aS.val t + bS.val t + bS.val t).toNat)
    (.bitsInput 8 0) ⟨by decide, rfl, by decide⟩
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      show Meaning (inputValues p.bools p.bits) (nestedE (.fvar i0) (.fvar i1) (.fvar i2))
        (.bits 8 (BitVec.ofNat 8 (aS.val t + bS.val t + bS.val t).toNat))
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact leafM)
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    (fun j hj => by
      intro we fuel
      show Contract (translateFuelFix translateStep fuel) p.context
        (inputValues p.bools p.bits) we mems initial
        (nestedE (.fvar i0) (.fvar i1) (.fvar i2))
        (.bits 8 (BitVec.ofNat 8 (aS.val t + bS.val t + bS.val t).toNat))
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact leafC we fuel)
    rfl
  obtain ⟨⟨result, hev, hout⟩, -⟩ := value
  refine ⟨result, hev, ?_⟩
  rw [hout]
  show (BitVec.ofNat 8 (aS.val t + bS.val t + bS.val t).toNat).toNat =
    (aS.val t + bS.val t + bS.val t).toNat
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

open Sparkle.IR.AST in
run_cmd liftTermElabM do
  -- The compiled parent and child are EXACTLY the canonical shapes.
  let (mp, d) ← synthesizeCombinationalCore ``parentUse [] false
  unless d.modules.length == 1 do
    throwError "hierarchical design departed from one child: {d.modules.map (·.name)}"
  let some cm := d.modules.head? | throwError "no child module"
  unless cm == childModule do
    throwError "child module departed from the pinned module (name included)"
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
  -- Three-input parent (the n-ary contract's witness): gate-accepted, and
  -- the certified dispatch agrees with the legacy front end byte-for-byte.
  unless (mixedCertifiedShape? false [] (← getConstInfo ``parentUse3) pred).isSome do
    throwError "three-input parent missed the instance gate"
  let (m3, d3) ← synthesizeCombinationalCore ``parentUse3 [] false
  let (m3L, d3L) ← synthesizeCombinationalCoreWith
    (fun e h t n => translateExprToWire e h t n) ``parentUse3 [] false
    (certifiedFrontEnd := false)
  unless m3.body == m3L.body && m3.inputs == m3L.inputs && m3.outputs == m3L.outputs &&
      m3.wires == m3L.wires && d3.modules == d3L.modules do
    throwError "three-input certified lowering departed from the legacy front end"
  unless mixedGateResultScalar (← getConstInfo ``parentUse3).type do
    throwError "parentUse3's result type is not one scalar Signal"
  -- Two-data-port sequential parent (the general contract's witness):
  -- gate-accepted, certified == legacy byte-for-byte incl. clk/rst.
  unless (mixedCertifiedShape? false [] (← getConstInfo ``parentSeq2) pred).isSome do
    throwError "two-port sequential parent missed the instance gate"
  let (mq, dq) ← synthesizeCombinationalCore ``parentSeq2 [] false
  let (mqL, dqL) ← synthesizeCombinationalCoreWith
    (fun e h t n => translateExprToWire e h t n) ``parentSeq2 [] false
    (certifiedFrontEnd := false)
  unless mq.body == mqL.body && mq.inputs == mqL.inputs && mq.outputs == mqL.outputs &&
      mq.wires == mqL.wires && dq.modules == dqL.modules do
    throwError "two-port sequential certified lowering departed from the legacy front end"
  unless mixedGateResultScalar (← getConstInfo ``parentSeq2).type do
    throwError "parentSeq2's result type is not one scalar Signal"
  -- Record-result parent: the scalar-result guard must keep it on the
  -- legacy path, which preserves BOTH outputs.
  unless (mixedCertifiedShape? false [] (← getConstInfo ``parentTwo) pred).isNone do
    throwError "record-result parent leaked through the instance gate"
  let (mt, _) ← synthesizeCombinationalCore ``parentTwo [] false
  unless mt.outputs.map (·.name) == ["lo", "hi"] do
    throwError "record-result parent lost an output: {mt.outputs.map (·.name)}"
  -- Projection parents of the two-output child: gate-accepted, certified
  -- == legacy byte-for-byte, ONE instance with both outputs wired, and a
  -- 16-case numeric regression of the linked semantics per field.
  for (nm, isHi) in [(``parentLo, false), (``parentHi, true)] do
    unless (mixedCertifiedShape? false [] (← getConstInfo nm) pred).isSome do
      throwError "projection parent {nm} missed the instance gate"
    unless mixedGateResultScalar (← getConstInfo nm).type do
      throwError "{nm}'s result type is not one scalar Signal"
    let (mj, dj) ← synthesizeCombinationalCore nm [] false
    let (mjL, djL) ← synthesizeCombinationalCoreWith
      (fun e h t n => translateExprToWire e h t n) nm [] false
      (certifiedFrontEnd := false)
    unless mj.body == mjL.body && mj.inputs == mjL.inputs && mj.outputs == mjL.outputs &&
        mj.wires == mjL.wires && dj.modules == djL.modules do
      throwError "projection parent {nm}: certified lowering departed from the legacy front end"
    let some cj := dj.modules.head? | throwError "no multi-output child module"
    unless dj.modules.length == 1 && cj == childTwoModule do
      throwError "multi-output child departed from the pinned module (name included)"
    let [Stmt.inst _ _ connsJ, Stmt.assign "out" (.ref _)] := mj.body |
      throwError "projection parent body departed from the instance-plus-alias shape"
    unless connsJ.map (·.1) == ["_gen_x", "_gen_y", "lo", "hi"] do
      throwError "projection parent does not wire every child port: {connsJ.map (·.1)}"
    let weJ : WEnv := fun n => if n == "out" || (mj.wires.any (·.name == n)) then 8 else 0
    let mut countJ : Nat := 0
    for av in List.range 4 do
      for bv in List.range 4 do
        let a := (63 * av + 11) % 256
        let b := (97 * bv + 5) % 256
        let env0 : Env := fun n =>
          if n == "_gen_a" then a else if n == "_gen_b" then b else 0
        let some envF := evalAssignsH weJ childrenTwo (fun _ _ => 0) mj.body env0 |
          throwError "projection linked elaboration failed at {a},{b}"
        let expect := if isHi then (a + 256 - b) % 256 else (a + b) % 256
        unless envF "out" == expect do
          throwError "projection linked out mismatch for {nm} at {a},{b}: {envF "out"}"
        countJ := countJ + 1
    unless countJ == 16 do throwError "projection case count mismatch"
  -- The projection boundaries' static facts HOLD in this environment.
  unless (← getEnv).getProjectionStructureName? ``TwoOut.hi == some ``TwoOut do
    throwError "TwoOut.hi is not a projection of TwoOut"
  unless (← projFieldName? ``TwoOut.hi ``TwoOut) == some "hi" do
    throwError "TwoOut.hi does not resolve to field hi"
  unless !Sparkle.Compiler.isHardwareModule (← getEnv) ``TwoOut.hi do
    throwError "projection function is tagged as a hardware module"
  -- Cones over instance leaves: gate-accepted at the run's predicate, and the
  -- certified front end agrees with the legacy one byte-for-byte (two calls,
  -- a repeated call deduped through the validated record, a Bool root, a
  -- sequential child inside a cone).
  for nm in [``parentMix, ``parentTwoCalls, ``parentRepeat, ``parentCmp, ``parentSeqMix,
      ``parentNested, ``parentPipeSeq, ``parentProjLeaf, ``parentProjArg] do
    unless (mixedCertifiedShape? false [] (← getConstInfo nm) pred).isSome do
      throwError "cone parent {nm} missed the instance-leaf gate"
    unless mixedGateResultScalar (← getConstInfo nm).type do
      throwError "{nm}'s result type is not one scalar Signal"
    let (mk, dk) ← synthesizeCombinationalCore nm [] false
    let (mkL, dkL) ← synthesizeCombinationalCoreWith
      (fun e h t n => translateExprToWire e h t n) nm [] false
      (certifiedFrontEnd := false)
    unless mk.body == mkL.body && mk.inputs == mkL.inputs && mk.outputs == mkL.outputs &&
        mk.wires == mkL.wires && dk.modules == dkL.modules do
      throwError "cone parent {nm}: certified lowering departed from the legacy front end"
  -- The pipeline parent: two instance statements, and the linked evaluation
  -- of the real compile computes (a + b) + b on 16 cases.
  let (mn2, dn2) ← synthesizeCombinationalCore ``parentNested [] false
  unless dn2.modules == [childModule] do
    throwError "parentNested's design is not exactly the pinned child"
  unless (mn2.body.filter (fun st => match st with | .inst .. => true | _ => false)).length == 2 do
    throwError "pipeline parent does not hold two instance statements"
  let weN := Tools.ShippingMixedEntrySoundness.moduleWidths mn2
  let mut countN : Nat := 0
  for av in List.range 4 do
    for bv in List.range 4 do
      let a := (63 * av + 11) % 256
      let b := (97 * bv + 5) % 256
      let env0 : Env := fun n =>
        if n == "_gen_a" then a else if n == "_gen_b" then b else 0
      let some envF := evalAssignsH weN (childrenOf childModule.name) (fun _ _ => 0)
          mn2.body env0 | throwError "parentNested linked elaboration failed at {a},{b}"
      unless envF "out" == (a + b + b) % 256 do
        throwError "parentNested linked out mismatch at {a},{b}: {envF "out"}"
      countN := countN + 1
  unless countN == 16 do throwError "pipeline case count mismatch"
  -- parentMix: the linked evaluation of the real compile, 16 cases, and the
  -- repeated call emits ONE instance.
  let (mx, dx) ← synthesizeCombinationalCore ``parentMix [] false
  unless dx.modules == [childModule] do
    throwError "parentMix's design is not exactly the pinned child"
  let (mrp, _) ← synthesizeCombinationalCore ``parentRepeat [] false
  unless (mrp.body.filter (fun st => match st with | .inst .. => true | _ => false)).length == 1 do
    throwError "repeated call did not dedupe to one instance"
  let weX := Tools.ShippingMixedEntrySoundness.moduleWidths mx
  let mut countX : Nat := 0
  for av in List.range 4 do
    for bv in List.range 4 do
      let a := (63 * av + 11) % 256
      let b := (97 * bv + 5) % 256
      let env0 : Env := fun n =>
        if n == "_gen_a" then a else if n == "_gen_b" then b else 0
      let some envF := evalAssignsH weX (childrenOf childModule.name) (fun _ _ => 0)
          mx.body env0 | throwError "parentMix linked elaboration failed at {a},{b}"
      unless envF "out" == (a + b + a) % 256 do
        throwError "parentMix linked out mismatch at {a},{b}: {envF "out"}"
      countX := countX + 1
  unless countX == 16 do throwError "cone case count mismatch"
  -- WIDTH LINKAGE. Every instance statement of every compiled parent of this
  -- file is linked against its child in the emitted design; a width-generic
  -- child instantiated at its compiled width passes, and at any other width
  -- the compile is REFUSED (it used to connect 16-bit wires to 8-bit ports).
  for nm in [``parentUse, ``parentUse3, ``parentSeq, ``parentSeq2, ``parentTwo, ``parentLo,
      ``parentHi, ``parentMix, ``parentTwoCalls, ``parentRepeat, ``parentCmp, ``parentSeqMix,
      ``parentNested, ``parentPipeSeq, ``parentProjLeaf, ``parentProjArg, ``parentW8] do
    let (ml, dl) ← synthesizeCombinationalCore nm [] false
    unless designLinked ml dl do
      throwError "{nm}: an instance statement is not width-linked"
  let refused ← try
      let _ ← synthesizeCombinationalCore ``parentW16 [] false
      pure false
    catch _ => pure true
  unless refused do
    throwError "a width-generic child instantiated at another width was not refused"
  -- 12-cycle SEQUENTIAL linked regression: the real parentSeq/childSeq
  -- pair, driven through `runH`, shows the register-delay behaviour on
  -- `out` (init 0, out_{j+1} = in_j), with the child's state threaded
  -- by the linked semantics itself.
  let (msq, dsq) ← synthesizeCombinationalCore ``parentSeq [] false
  let some mcSeq := dsq.modules.head? | throwError "no sequential child module"
  unless msq.body == instBody mcSeq.name
      "_tmp_inst_Sparkle_Tests_Compiler_ShippingHierarchySoundnessTest_childSeq_0"
      [("clk", .ref "clk"), ("rst", .ref "rst"), ("_gen_x", .ref "_gen_a")]
      "out" "_gen_out" do
    throwError "sequential parent body departed from the canonical instBody"
  let childrenSeq : String → Option (Sparkle.IR.AST.Module × WEnv) := fun n =>
    if n = mcSeq.name then some (mcSeq, Tools.ShippingEntrySoundness.weOf mcSeq) else none
  let kk := 12
  let inVal : Nat → Nat := fun wall => (37 * wall + 9) % 256
  let seedP : Nat → Env := fun t => fun n =>
    if n == "_gen_a" then inVal (kk - 1 - t) else 0
  let weP : WEnv := fun n =>
    if n == "_gen_a" || n == "_gen_out" || n == "out" then 8 else
    if n == "clk" || n == "rst" then 1 else 0
  let some trace := runH weP childrenSeq msq.body seedP kk (fun _ => 0) (fun _ _ => 0)
    | throwError "sequential linked run failed"
  unless trace.length == kk do throwError "linked trace length mismatch"
  let mut expected : Nat := 0
  let mut wall := 0
  for env in trace do
    unless env "out" == expected do
      throwError "linked seq out mismatch at {wall}: {env "out"} ≠ {expected}"
    expected := inVal wall
    wall := wall + 1
  -- The retained scalar-type premises HOLD for the real declarations.
  unless mixedGateResultScalar (← getConstInfo ``parentUse).type do
    throwError "parentUse's result type is not one scalar Signal"
  unless mixedGateResultScalar (← getConstInfo ``parentSeq).type do
    throwError "parentSeq's result type is not one scalar Signal"
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
      ``parentUse_peel, ``parentUse_instance_entry, ``parentUse_entry_observes,
      ``Tools.ShippingInstanceEntrySoundness.synthesizeMixedCertified_instance1_sound,
      ``Tools.ShippingInstanceEntrySoundness.instance1_entry_of_env,
      ``parentSeq_peel, ``parentSeq_instance_entry,
      ``Tools.ShippingInstanceEntrySoundness.instArgs_resolve,
      ``Tools.ShippingInstanceEntrySoundness.synthesizeMixedCertified_instanceN_sound,
      ``Tools.ShippingInstanceEntrySoundness.instanceN_entry_of_env,
      ``parentUse3_peel, ``parentUse3_instance_entry,
      ``Tools.ShippingInstanceEntrySoundness.instClkRst_pure,
      ``Tools.ShippingInstanceEntrySoundness.synthesizeMixedCertified_instanceG_sound,
      ``Tools.ShippingInstanceEntrySoundness.instanceG_entry_of_env,
      ``parentSeq2_peel, ``parentSeq2_instance_entry,
      ``Tools.ShippingInstanceEntrySoundness.instanceProj_term_gate,
      ``Tools.ShippingInstanceEntrySoundness.instanceProj_step,
      ``Tools.ShippingInstanceEntrySoundness.instCallKey_returns,
      ``Tools.ShippingInstanceEntrySoundness.instOutWires_pure,
      ``Tools.ShippingInstanceEntrySoundness.outWireNames_nodup,
      ``Tools.ShippingInstanceEntrySoundness.projUncached_run,
      ``Tools.ShippingInstanceEntrySoundness.synthesizeMixedCertified_instanceProj_sound,
      ``Tools.ShippingInstanceEntrySoundness.synthesizeFromConst_instanceProj_sound,
      ``Tools.ShippingInstanceEntrySoundness.instanceProj_entry_of_env,
      ``Tools.ShippingHierarchySoundness.instAlias_linked,
      ``parentHi_peel, ``parentHi_instance_entry, ``parentHi_entry_observes,
      ``Tools.ShippingLinkCtx.evalAssignsH_append,
      ``Tools.ShippingUnifiedMeaning.Meaning.deterministic,
      ``Tools.ShippingUnifiedMeaning.meaning_quote_leaves,
      ``Tools.ShippingUnifiedRecursion.fuel_contract_leaves,
      ``Tools.ShippingInstanceLeaf.runs_inst,
      ``Tools.ShippingInstanceLeaf.instArgs_sem,
      ``Tools.ShippingInstanceLeaf.instUncached_shape,
      ``Tools.ShippingInstanceLeaf.inst_leaf_contract,
      ``Tools.ShippingInstanceLeaf.inst_leaf_fuel,
      ``Tools.ShippingHierTermSoundness.hier_quote_accepted,
      ``Tools.ShippingHierTermSoundness.hier_root_accepted,
      ``Tools.ShippingHierTermSoundness.hier_cone_gate,
      ``Tools.ShippingHierTermSoundness.synthesizeMixedCertified_hierCone_sound,
      ``Tools.ShippingHierTermSoundness.synthesizeFromConst_hierCone_sound,
      ``Tools.ShippingHierTermSoundness.hierCone_entry_of_env,
      ``parentMix_peel, ``childAdd_correct, ``parentMix_entry_observes,
      ``Tools.ShippingLinkCtx.instLinked_sound,
      ``Tools.ShippingLinkCtx.Linked.mono,
      ``Tools.ShippingInstanceEntrySoundness.instLinkCheck_returns,
      ``Tools.ShippingHierTermSoundness.hier_instRoot_gate,
      ``Tools.ShippingHierTermSoundness.hierRoot_entry_of_env,
      ``parentNested_peel, ``parentNested_entry_observes,
      ``Tools.ShippingHierarchySoundness.instBody_runH, ``childSeq_run,
      ``parentSeq_runH_observes,
      ``parentUse_linked] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected hierarchy soundness axiom: {name}: {ax}"
  logInfo "HIERARCHY FOUNDATION: canonical parent/child pinned; linked semantics matches; standard axioms only"

end Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
