import Tools.ShippingInstanceLeaf

/-! # Instance calls read by the COMPILER's rule: the last #ports arguments

Worker W, unit 1 (BUILT, round 1) and round 2 (WRITTEN, NOT BUILT): the
meaning is extended IN PLACE (ruling 2026-10-15: the extension to calls
without a domain argument is ALLOWED; the old definitions are kept as a
compatibility layer).

The compiler's single-output instance arm (`translateInstanceUncachedWith`,
`Sparkle/Compiler/Elab.lean`) connects the child's non-clk/rst input ports to
the LAST `#ports` arguments of the call's spine:
`inputPorts.zip (args.drop (args.length - inputPorts.length))`. Whatever comes
before them (an implicit domain, a width argument of a width-generic child, or
nothing at all, as in `pick sel x`) is not connected.

Round 2: `Tools.ShippingUnifiedMeaning.Meaning.inst` now reads an instance
call by that rule (`instSpineArgs e = pre ++ args`,
`args.length = ChildSem.ports mn`, any `pre`); `ChildSem` carries the port
count `ports` beside the child semantics. This file keeps:

* THE COMPATIBILITY LAYER: `MeaningD`, the old domain-carrying definition
  verbatim (`instSpineArgs e = dom :: args`: EXACTLY ONE leading argument
  dropped), `MeaningD.deterministic`; under `ArityOK` (the child semantics is
  defined only at its port count — satisfied by the existing `addSem`, see
  `Tests/Compiler/WrapPickMeaningTest.lean`) every old meaning is a new one
  with the same value (`meaning_of_meaningD`), hence on every expression the
  old meaning is defined the new one is defined with EXACTLY that value and no
  other (`meaningD_agree`);
* `no_meaningD_of_portsSpine` — the round-1 finding as a theorem: under
  `ArityOK`, a call whose spine has exactly `ports mn` arguments (no leading
  argument) has NO old meaning at all;
* `inst_args_eq` (the arguments an instance meaning reads are the compiler's),
  `meaning_inst_cons` (one leading argument is the prefix `[dom]`),
  `meaning_instP` (the meaning of `instEP`), `instEP_eq_instEN`;
* the compiler side for any leading prefix: `instEP` (the n-ary call with any
  prefix), `instUncached_shapeE` (`instUncached_shape` for
  `instSpineArgs e = pre ++ argsE`; the old one is the corollary
  `instUncached_shape_of_E` at `pre = [dom]`), and `instUncached_linkedE`
  (the emitted statement is in the body and width-linked: every connected
  parent wire is declared at exactly its port's width).

Removed in round 2 (subsumed by the in-place `Meaning`): the round-1
`ChildPorts` class, `MeaningP`, `MeaningP.inst_args`, `MeaningP.deterministic`,
`MeaningP.inst_cons`, `meaningP_of_meaning`, `meaningP_agree`,
`no_meaning_of_portsSpine`, `LeafMeaningP` (their content is `Meaning`,
`inst_args_eq`, `Meaning.deterministic`, `meaning_inst_cons`,
`meaning_of_meaningD`, `meaningD_agree`, `no_meaningD_of_portsSpine`). -/
namespace Tools.ShippingInstanceMeaningP
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingLinkCtx (Linked instLinked_sound)
open Tools.ShippingInstanceEntrySoundness

set_option linter.unusedSectionVars false

/-! ## The call with any leading prefix -/

/-- The n-ary call `@mn p₁ … pₖ a₁ … aₙ`: the prefix `pre` (domain, width
arguments, or nothing), then the arguments. -/
def instEP (mn : Name) (lvls : List Level) (pre args : List Lean.Expr) : Lean.Expr :=
  args.foldl (fun f a => .app f a) (pre.foldl (fun f a => .app f a) (.const mn lvls))

theorem instEP_spineArgs (mn : Name) (lvls : List Level) (pre args : List Lean.Expr) :
    instSpineArgs (instEP mn lvls pre args) = pre ++ args := by
  unfold instEP
  rw [spineArgs_foldl, spineArgs_foldl]
  rfl

theorem instEP_getAppFn (mn : Name) (lvls : List Level) (pre args : List Lean.Expr) :
    (instEP mn lvls pre args).getAppFn = .const mn lvls := by
  unfold instEP
  rw [getAppFn_foldl, getAppFn_foldl]
  rfl

/-- The domain-carrying call is the prefix `[dom]`. -/
theorem instEN_eq_instEP (mn : Name) (lvls : List Level) (dom : Lean.Expr)
    (args : List Lean.Expr) : instEN mn lvls dom args = instEP mn lvls [dom] args := rfl

/-- A call with a non-empty spine `d :: rest` is the domain-carrying call on
its first spine argument, however the spine is split into prefix and ports. -/
theorem instEP_eq_instEN (mn : Name) (lvls : List Level) {pre args : List Lean.Expr}
    {d : Lean.Expr} {rest : List Lean.Expr} (h : pre ++ args = d :: rest) :
    instEP mn lvls pre args = instEN mn lvls d rest := by
  unfold instEP instEN
  rw [← List.foldl_append, h]
  try rfl

/-- THE COMPILER'S RULE: when the spine is `pre ++ args` with `args` of the
port count, the arguments the arm connects (`drop (length - #ports)`) are
`args`. -/
theorem portArgs_eq {e : Lean.Expr} {pre args : List Lean.Expr} {k : Nat}
    (hsp : instSpineArgs e = pre ++ args) (hk : args.length = k) :
    (instSpineArgs e).drop ((instSpineArgs e).length - k) = args := by
  subst hk
  rw [hsp, List.length_append, Nat.add_sub_cancel]
  exact List.drop_left

/-! ## The new meaning: helpers -/

section meaning
variable [ChildSem]

/-- The arguments an instance meaning reads are the compiler's. -/
theorem inst_args_eq {e : Lean.Expr} {mn : Name} {pre args : List Lean.Expr}
    (hsp : instSpineArgs e = pre ++ args) (hports : args.length = ChildSem.ports mn) :
    args = (instSpineArgs e).drop ((instSpineArgs e).length - ChildSem.ports mn) :=
  (portArgs_eq hsp hports).symm

/-- One leading argument is the prefix `[dom]`. -/
theorem meaning_inst_cons {inputs : FVarId → Option Value} {e : Lean.Expr} {mn : Name}
    {lvls : List Level} {dom : Lean.Expr} {args : List Lean.Expr} {vs : List Value} {v : Value}
    (hview : view e = none) (hfn : e.getAppFn = .const mn lvls)
    (hsp : instSpineArgs e = dom :: args) (hports : args.length = ChildSem.ports mn)
    (hlen : vs.length = args.length)
    (hargs : ∀ i (ha : i < args.length) (hv : i < vs.length),
      Meaning inputs (args[i]'ha) (vs[i]'hv))
    (hsem : ChildSem.childSem mn vs = some v) : Meaning inputs e v :=
  .inst (pre := [dom]) hview hfn hsp hports hlen hargs hsem

/-- The meaning of a call with any prefix: the child's source function of its
PORT arguments' meanings. -/
theorem meaning_instP {inputs : FVarId → Option Value} {mn : Name} {lvls : List Level}
    {pre argsE : List Lean.Expr} {vs : List Value} {v : Value}
    (hview : view (instEP mn lvls pre argsE) = none)
    (hports : argsE.length = ChildSem.ports mn)
    (hlen : argsE.length = vs.length)
    (hargs : ∀ k (hk : k < argsE.length) (hk' : k < vs.length),
      Meaning inputs (argsE[k]'hk) (vs[k]'hk'))
    (hsem : ChildSem.childSem mn vs = some v) :
    Meaning inputs (instEP mn lvls pre argsE) v :=
  .inst hview (instEP_getAppFn mn lvls pre argsE) (instEP_spineArgs mn lvls pre argsE)
    hports hlen.symm hargs hsem

/-! ## The compatibility layer: the old, domain-carrying meaning -/

/-- **The OLD meaning, verbatim** (`Tools.ShippingUnifiedMeaning.Meaning` up
to round 1): an instance call drops EXACTLY ONE leading spine argument. -/
inductive MeaningD (inputs : FVarId → Option Value) : Lean.Expr → Value → Prop where
  | input {e id v} : view e = some (.input id) → inputs id = some v → MeaningD inputs e v
  | value {e v} : view e = some (.value v) → MeaningD inputs e v
  | binary {e op a b va vb v} : view e = some (.binary op a b) →
      MeaningD inputs a va → MeaningD inputs b vb → op.run va vb = some v → MeaningD inputs e v
  | boolNot {e a b} : view e = some (.boolNot a) → MeaningD inputs a (.bool b) →
      MeaningD inputs e (.bool (!b))
  | mux {e kind c a b vc va vb v} : view e = some (.mux kind c a b) →
      MeaningD inputs c vc → MeaningD inputs a va → MeaningD inputs b vb →
      muxValue kind vc va vb = some v → MeaningD inputs e v
  | setw {e w w' a va v} : view e = some (.setw w w' a) →
      MeaningD inputs a va → setwValue w w' va = some v → MeaningD inputs e v
  | slice {e w start len a va v} : view e = some (.slice w start len a) →
      MeaningD inputs a va → sliceValue w start len va = some v → MeaningD inputs e v
  | concat {e m n a b va vb v} : view e = some (.concat m n a b) →
      MeaningD inputs a va → MeaningD inputs b vb → concatValue m n va vb = some v →
      MeaningD inputs e v
  | inst {e mn lvls dom args vs v} : view e = none → e.getAppFn = .const mn lvls →
      instSpineArgs e = dom :: args → vs.length = args.length →
      (∀ i (ha : i < args.length) (hv : i < vs.length),
        MeaningD inputs (args[i]'ha) (vs[i]'hv)) →
      ChildSem.childSem mn vs = some v → MeaningD inputs e v

/-- The old determinism proof, verbatim. -/
theorem MeaningD.deterministic {inputs e a b} (ha : MeaningD inputs e a)
    (hb : MeaningD inputs e b) : a = b := by
  induction ha generalizing b with
  | inst hview hfn hsp hlen hargs hsem ih =>
    cases hb with
    | inst hview' hfn' hsp' hlen' hargs' hsem' =>
      have hc := Lean.Expr.const.inj (hfn.symm.trans hfn')
      have hs := List.cons.inj (hsp.symm.trans hsp')
      obtain ⟨hmn, -⟩ := hc
      obtain ⟨-, hargsEq⟩ := hs
      subst hmn hargsEq
      have hvs := List.ext_getElem (hlen.trans hlen'.symm) (fun i h1 h2 =>
        ih i (by rw [← hlen]; exact h1) h1 (hargs' i (by rw [← hlen]; exact h1) h2))
      subst hvs
      exact Option.some.inj (hsem.symm.trans hsem')
    | _ => simp_all
  | _ => cases hb <;> grind

/-- The child semantics is defined only at each callee's port count. A
property of the consumer's `ChildSem`, discharged per semantics by
evaluation (`addSem_arityOK`, `pickSem_arityOK`), never assumed. -/
def ArityOK : Prop :=
  ∀ (mn : Name) (vs : List Value) (v : Value),
    ChildSem.childSem mn vs = some v → vs.length = ChildSem.ports mn

/-- **Compatibility, part 1**: every old meaning is a new meaning, at the
same value. -/
theorem meaning_of_meaningD (hA : ArityOK) {inputs : FVarId → Option Value}
    {e : Lean.Expr} {v : Value} (h : MeaningD inputs e v) : Meaning inputs e v := by
  induction h with
  | input hv hi => exact .input hv hi
  | value hv => exact .value hv
  | binary hv _ _ hr iha ihb => exact .binary hv iha ihb hr
  | boolNot hv _ iha => exact .boolNot hv iha
  | mux hv _ _ _ hm ihc iha ihb => exact .mux hv ihc iha ihb hm
  | setw hv _ hs iha => exact .setw hv iha hs
  | slice hv _ hs iha => exact .slice hv iha hs
  | concat hv _ _ hc iha ihb => exact .concat hv iha ihb hc
  | inst hview hfn hsp hlen _ hsem ih =>
    exact meaning_inst_cons hview hfn hsp (hlen.symm.trans (hA _ _ _ hsem)) hlen ih hsem

/-- **Compatibility, part 2 (the meaning is unchanged where the old one is
defined)**: on an expression with an old meaning `v`, the new meanings are
exactly `v`. -/
theorem meaningD_agree (hA : ArityOK) {inputs : FVarId → Option Value}
    {e : Lean.Expr} {v : Value} (h : MeaningD inputs e v) (v' : Value) :
    Meaning inputs e v' ↔ v' = v :=
  ⟨fun h' => Meaning.deterministic h' (meaning_of_meaningD hA h),
   fun eq => eq ▸ meaning_of_meaningD hA h⟩

/-- **The round-1 finding, as a theorem**: under `ArityOK`, a call whose
spine is exactly its port arguments (no domain, no prefix: `pick sel x`) has
NO old meaning — `MeaningD.inst` would read one argument fewer than the child
semantics is defined at. -/
theorem no_meaningD_of_portsSpine (hA : ArityOK) {inputs : FVarId → Option Value}
    {e : Lean.Expr} {v : Value} {mn : Name} {lvls : List Level}
    (hview : view e = none) (hfn : e.getAppFn = .const mn lvls)
    (hports : (instSpineArgs e).length = ChildSem.ports mn) :
    ¬ MeaningD inputs e v := by
  intro h
  cases h with
  | inst hview' hfn' hsp hlen hargs hsem =>
    have hc := Lean.Expr.const.inj (hfn.symm.trans hfn')
    obtain ⟨hmn, -⟩ := hc
    subst hmn
    have h1 := hA _ _ _ hsem
    rw [hsp, List.length_cons] at hports
    omega
  | _ => simp_all

end meaning

/-! ## The compiler side for any prefix -/

theorem filter_noclkP {ps : List Port}
    (h : ∀ p ∈ ps, (p.name == "clk") = false ∧ (p.name == "rst") = false) :
    ps.filter (fun p => p.name != "clk" && p.name != "rst") = ps := by
  rw [List.filter_eq_self]
  intro p hp
  obtain ⟨h1, h2⟩ := h p hp
  simp [bne, h1, h2]

/-- **`instUncached_shape` for a call with ANY prefix**: the spine is
`pre ++ argsE` with `argsE` of the child's port count. The arm connects
`argsE` (the compiler's last-#ports rule), then either a validated cache hit
returns a wire recorded for this very expression, or a fresh wire is
allocated and ONE width-linked instance statement emitted. -/
theorem instUncached_shapeE {rec : TranslateFn} {ctx : CompilerState} {mn : Name}
    {mc : Sparkle.IR.AST.Module} {dc : Design} {so : Port}
    {e : Lean.Expr} {pre argsE : List Lean.Expr}
    {hint : String} {top named : Bool} {s t : CircuitState} {w : String}
    (hdc : dc.modules = [])
    (hnoclk : ∀ p ∈ mc.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hsp : instSpineArgs e = pre ++ argsE)
    (hlen : mc.inputs.length = argsE.length)
    (run : Returns (translateInstanceUncachedWith rec mn mc dc so e hint top named) ctx s w t) :
    ∃ (d' : Design) (conns : List (String × Sparkle.IR.AST.Expr)) (sA : CircuitState),
      Returns (instArgs rec [] (mc.inputs.zip argsE) 0) ctx { s with design := d' } conns sA ∧
      ((instHitValid s.translateRecord e w = true ∧ t = sA) ∨
       (∃ iname : String, w = (CircuitM.makeWire hint so.ty named sA).1 ∧
         t = { (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2 with
           module := (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module.addStmt
             (.inst mc.name iname (conns.reverse ++ [(so.name, .ref w)])) } ∧
         instLinked (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module mc
           (conns.reverse ++ [(so.name, .ref w)]) = true)) := by
  rw [instanceUncached_run] at run
  obtain ⟨cs0, sG, hget0, k1⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) run
  obtain ⟨hcs0, hsG⟩ := Returns.get hget0
  rw [hcs0, hsG] at k1
  rw [hdc] at k1
  obtain ⟨u0, sA0, hAdd0, k2⟩ := Returns.bind (m := instAddModules _ []) k1
  obtain ⟨-, hsA0⟩ := Returns.pure (by exact hAdd0 : Returns (pure ()) _ _ u0 sA0)
  rw [hsA0] at k2
  obtain ⟨uR, sB, hReg, k3⟩ := Returns.bind (m := instRegisterChild _ mc) k2
  have hsB : ∃ d', sB = { s with design := d' } := by
    unfold instRegisterChild at hReg
    obtain ⟨cs, s1, hget, k⟩ := Returns.bind (m := (get : CompilerM CircuitState)) hReg
    obtain ⟨hcs, hs1⟩ := Returns.get hget
    rw [hcs, hs1] at k
    split at k
    · exact ⟨_, addModuleToDesignC_returns k⟩
    · obtain ⟨-, hs⟩ := Returns.pure k
      exact ⟨s.design, hs⟩
  obtain ⟨d', hsB⟩ := hsB
  obtain ⟨conns0, sC, hClk, k4⟩ := Returns.bind (m := instClkRst [] mc.inputs) k3
  obtain ⟨hconns0, hsC⟩ := instClkRst_skip hnoclk hClk
  rw [filter_noclkP hnoclk, hsp] at k4
  obtain ⟨uG, sH, hGuard, k5⟩ := Returns.bind (m := instArityCheck mn _ _) k4
  unfold instArityCheck at hGuard
  rw [if_neg (by
    rw [List.length_append, hlen]
    exact Nat.not_lt.mpr (Nat.le_add_left _ _))] at hGuard
  obtain ⟨-, hsH⟩ := Returns.pure hGuard
  have hdrop : (pre ++ argsE).drop ((pre ++ argsE).length - mc.inputs.length) = argsE := by
    rw [hlen, List.length_append, Nat.add_sub_cancel]
    exact List.drop_left
  rw [hdrop, hconns0] at k5
  obtain ⟨conns, sF, hArgs, k6⟩ := Returns.bind (m := instArgs _ _ _ 0) k5
  rw [hsH, hsC, hsB] at hArgs
  refine ⟨d', conns, sF, hArgs, ?_⟩
  obtain ⟨csP, sP2, hgetP, k7⟩ :=
    Returns.bind (m := (get : CompilerM CircuitState)) k6
  obtain ⟨hcsP, hsP2⟩ := Returns.get hgetP
  obtain ⟨cVal, sQ, hCacheRead, k8⟩ :=
    Returns.bind (m := CompilerM.liftMetaM instArmCacheGet) k7
  have hsQ := Returns.liftMetaM hCacheRead
  cases hhit : (cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
      (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}").filter
      (instHitValid s.translateRecord e) with
  | some cw =>
    rw [hhit] at k8
    obtain ⟨hw, ht⟩ := Returns.pure k8
    left
    refine ⟨?_, by rw [ht, hsQ, hsP2]⟩
    rw [hw]
    cases hget : cVal.get? s!"{csP.module.name}#{mc.name}#{String.intercalate ";"
        (conns.reverse.map (fun (p, rhs) => s!"{p}={rhs}"))}" with
    | none => rw [hget] at hhit; cases hhit
    | some c0 =>
      rw [hget] at hhit
      by_cases hv : instHitValid s.translateRecord e c0 = true
      · have : (some c0 : Option String) = some cw := by
          simpa [Option.filter, hv] using hhit
        cases this
        exact hv
      · simp [Option.filter, hv] at hhit
  | none =>
    rw [hhit] at k8
    simp only [] at k8
    obtain ⟨outW, sW, hMk, k9⟩ := Returns.bind (m := CompilerM.makeWire hint _ named) k8
    obtain ⟨houtW, hsW⟩ := makeWireC_returns hMk
    obtain ⟨uP, sV, hPut, k10⟩ :=
      Returns.bind (m := CompilerM.liftMetaM (instArmCachePut _ _)) k9
    have hsV := Returns.liftMetaM hPut
    obtain ⟨instName, sN, hFresh, k11⟩ := Returns.bind (m := CompilerM.freshName _) k10
    obtain ⟨hinstName, hsN⟩ := freshNameC_returns hFresh
    obtain ⟨uL, sL, hLink, k11⟩ := Returns.bind (m := instLinkCheck _ _ _) k11
    obtain ⟨hsL, hlinked⟩ := instLinkCheck_returns hLink
    rw [hsL] at k11
    obtain ⟨uE, sI, hEmit, k12⟩ :=
      Returns.bind (m := CompilerM.emitInstance mc.name _ _) k11
    have hsI := emitInstanceC_returns hEmit
    obtain ⟨hwEq, ht⟩ := Returns.pure k12
    right
    refine ⟨instName, ?_, ?_, ?_⟩
    · rw [hwEq, houtW, hsQ, hsP2]
    · rw [ht, hsI, hsN, hsV, hsW, hsQ, hsP2, hwEq]
      simp
    · rw [hsN, hsV, hsW, hsQ, hsP2, List.reverse_cons] at hlinked
      rw [hwEq]
      exact hlinked

/-- The old shape lemma is the prefix `[dom]` (agreement on the compiler
side: nothing about domain-carrying calls changes). -/
theorem instUncached_shape_of_E {rec : TranslateFn} {ctx : CompilerState} {mn : Name}
    {mc : Sparkle.IR.AST.Module} {dc : Design} {so : Port}
    {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {hint : String} {top named : Bool} {s t : CircuitState} {w : String}
    (hdc : dc.modules = [])
    (hnoclk : ∀ p ∈ mc.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hlen : mc.inputs.length = argsE.length)
    (run : Returns (translateInstanceUncachedWith rec mn mc dc so
      (instEN mn lvls dom argsE) hint top named) ctx s w t) :
    ∃ (d' : Design) (conns : List (String × Sparkle.IR.AST.Expr)) (sA : CircuitState),
      Returns (instArgs rec [] (mc.inputs.zip argsE) 0) ctx { s with design := d' } conns sA ∧
      ((instHitValid s.translateRecord (instEN mn lvls dom argsE) w = true ∧ t = sA) ∨
       (∃ iname : String, w = (CircuitM.makeWire hint so.ty named sA).1 ∧
         t = { (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2 with
           module := (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module.addStmt
             (.inst mc.name iname (conns.reverse ++ [(so.name, .ref w)])) } ∧
         instLinked (CircuitM.freshName s!"inst_{mc.name}" false
                (CircuitM.makeWire hint so.ty named sA).2).2.module mc
           (conns.reverse ++ [(so.name, .ref w)]) = true)) :=
  instUncached_shapeE (pre := [dom]) hdc hnoclk (instEN_spineArgs mn lvls dom argsE) hlen run

/-- **Argument width = port width, by the compiler's guard (not by typing)**:
an uncached lowering of a call with any prefix that returns either hit the
validated cache, or put ONE instance statement into the body whose every
connection is a parent name declared at EXACTLY its child port's width
(`Linked`). Lean's typing does not give this for width-generic children
(`childW 4 a b` type-checks against a child compiled at 8 bits; see
`Tests/Compiler/NarrowArgPortTest.lean`): it is `instLinkCheck`, run before
`emitInstance`, that refuses such a call. -/
theorem instUncached_linkedE {rec : TranslateFn} {ctx : CompilerState} {mn : Name}
    {mc : Sparkle.IR.AST.Module} {dc : Design} {so : Port}
    {e : Lean.Expr} {pre argsE : List Lean.Expr}
    {hint : String} {top named : Bool} {s t : CircuitState} {w : String}
    (hdc : dc.modules = [])
    (hnoclk : ∀ p ∈ mc.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false)
    (hsp : instSpineArgs e = pre ++ argsE)
    (hlen : mc.inputs.length = argsE.length)
    (run : Returns (translateInstanceUncachedWith rec mn mc dc so e hint top named) ctx s w t) :
    instHitValid s.translateRecord e w = true ∨
    ∃ (iname : String) (conns : List (String × Sparkle.IR.AST.Expr)),
      Stmt.inst mc.name iname conns ∈ t.module.body ∧ Linked t.module mc conns := by
  obtain ⟨d', conns, sA, -, hcase⟩ := instUncached_shapeE hdc hnoclk hsp hlen run
  rcases hcase with ⟨hv, -⟩ | ⟨iname, -, ht, hlk⟩
  · exact Or.inl hv
  · refine Or.inr ⟨iname, conns.reverse ++ [(so.name, .ref w)], ?_, ?_⟩
    · rw [ht]
      exact List.mem_cons_self
    · rw [ht]
      exact (instLinked_sound hlk).mono (fun q hq => hq) (fun q hq => hq)

end Tools.ShippingInstanceMeaningP

#print axioms Tools.ShippingInstanceMeaningP.instEP_eq_instEN
#print axioms Tools.ShippingInstanceMeaningP.meaning_instP
#print axioms Tools.ShippingInstanceMeaningP.MeaningD.deterministic
#print axioms Tools.ShippingInstanceMeaningP.meaning_of_meaningD
#print axioms Tools.ShippingInstanceMeaningP.meaningD_agree
#print axioms Tools.ShippingInstanceMeaningP.no_meaningD_of_portsSpine
#print axioms Tools.ShippingInstanceMeaningP.instUncached_shapeE
#print axioms Tools.ShippingInstanceMeaningP.instUncached_shape_of_E
#print axioms Tools.ShippingInstanceMeaningP.instUncached_linkedE
