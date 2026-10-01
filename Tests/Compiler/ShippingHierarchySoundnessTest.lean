import Tools.ShippingHierarchySoundness
import Tools.ShippingInstanceEntrySoundness
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

@[hardware_module] def childAdd {dom : DomainConfig}
    (x y : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := x + y

def parentUse {dom : DomainConfig} (a b : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd a b

/-- A three-input child and its parent: the n-ary instance contract. -/
@[hardware_module] def childAdd3 {dom : DomainConfig}
    (x y z : Signal dom (BitVec 8)) : Signal dom (BitVec 8) := x + y + z

def parentUse3 {dom : DomainConfig} (a b c : Signal dom (BitVec 8)) :
    Signal dom (BitVec 8) := childAdd3 a b c

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
    (hcache : InstanceCacheEmpty)
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
    ∃ envF, evalAssignsH we (childrenOf "childAdd") mems m.body env0 = some envF ∧
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
      htagAll hsub hcache hdc rfl rfl rfl rfl rfl rfl
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
    (children := childrenOf "childAdd")
    (mn := "childAdd") (instName := instName)
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
  -- Record-result parent: the scalar-result guard must keep it on the
  -- legacy path, which preserves BOTH outputs.
  unless (mixedCertifiedShape? false [] (← getConstInfo ``parentTwo) pred).isNone do
    throwError "record-result parent leaked through the instance gate"
  let (mt, _) ← synthesizeCombinationalCore ``parentTwo [] false
  unless mt.outputs.map (·.name) == ["lo", "hi"] do
    throwError "record-result parent lost an output: {mt.outputs.map (·.name)}"
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
      ``Tools.ShippingHierarchySoundness.instBody_runH, ``childSeq_run,
      ``parentSeq_runH_observes,
      ``parentUse_linked] do
    for ax in (← collectAxioms name) do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected hierarchy soundness axiom: {name}: {ax}"
  logInfo "HIERARCHY FOUNDATION: canonical parent/child pinned; linked semantics matches; standard axioms only"

end Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest
