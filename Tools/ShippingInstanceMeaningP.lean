import Tools.ShippingInstanceLeaf

/-! # Instance calls read by the COMPILER's rule: the last #ports arguments

WRITTEN, NOT BUILT. Worker W, unit 1 (ruling: extend the meaning to calls
without a domain argument).

The compiler's single-output instance arm (`translateInstanceUncachedWith`,
`Sparkle/Compiler/Elab.lean`) connects the child's non-clk/rst input ports to
the LAST `#ports` arguments of the call's spine:
`inputPorts.zip (args.drop (args.length - inputPorts.length))`. Whatever comes
before them (an implicit domain, a width argument of a width-generic child, or
nothing at all, as in `pick sel x`) is not connected.

The existing source meaning `Tools.ShippingUnifiedMeaning.Meaning` reads an
instance call as `instSpineArgs e = dom :: args`: EXACTLY ONE leading argument
is dropped. That is the compiler's rule only when the callee has one leading
non-port argument; for `pick sel x` (no domain binder) it reads `sel` as the
domain and `[x]` as the arguments.

This file adds, WITHOUT changing any existing definition:

* `ChildPorts` — the number of port arguments of each callee (the consumer's
  choice, like `ChildSem`; a leaf contract links it to the compiled child by
  `mc.inputs.length = ChildPorts.ports mn`);
* `MeaningP` — `Meaning` with the instance constructor reading
  `instSpineArgs e = pre ++ args`, `args.length = ChildPorts.ports mn`, any
  `pre` (`portArgs_eq`: these are exactly the compiler's arguments);
* `MeaningP.deterministic` — the cache-insertion obligation, as for `Meaning`;
* THE COMPATIBILITY LAYER: under `ArityOK` (the child semantics is defined
  only at its port count — satisfied by the existing `addSem`, see
  `Tests/Compiler/WrapPickMeaningTest.lean`), every `Meaning` is a `MeaningP`
  with the same value (`meaningP_of_meaning`), hence on every expression the
  old meaning is defined the new one is defined with EXACTLY that value and no
  other (`meaningP_agree`). The seven gate parents' theorems are stated over
  `Meaning` and are untouched;
* `no_meaning_of_portsSpine` — the finding as a theorem: under `ArityOK`, a
  call whose spine has exactly `ports mn` arguments (no leading argument) has
  NO old meaning at all;
* the compiler side for any leading prefix: `instEP` (the n-ary call with any
  prefix), `instUncached_shapeE` (`instUncached_shape` for
  `instSpineArgs e = pre ++ argsE`; the old one is the corollary
  `instUncached_shape_of_E` at `pre = [dom]`), and `instUncached_linkedE`
  (the emitted statement is in the body and width-linked: every connected
  parent wire is declared at exactly its port's width). -/
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

/-- THE COMPILER'S RULE: when the spine is `pre ++ args` with `args` of the
port count, the arguments the arm connects (`drop (length - #ports)`) are
`args`. -/
theorem portArgs_eq {e : Lean.Expr} {pre args : List Lean.Expr} {k : Nat}
    (hsp : instSpineArgs e = pre ++ args) (hk : args.length = k) :
    (instSpineArgs e).drop ((instSpineArgs e).length - k) = args := by
  subst hk
  rw [hsp, List.length_append, Nat.add_sub_cancel]
  exact List.drop_left

/-! ## The meaning -/

/-- The number of PORT arguments of each callee (what the compiled child's
non-clk/rst inputs count). The consumer's choice, as `ChildSem` is. -/
class ChildPorts where
  ports : Name → Nat

section meaning
variable [ChildSem] [ChildPorts]

/-- `Meaning`, with an instance call read by the compiler's rule: the last
`ChildPorts.ports mn` spine arguments, after ANY prefix. Every other
constructor is `Meaning`'s, verbatim. -/
inductive MeaningP (inputs : FVarId → Option Value) : Lean.Expr → Value → Prop where
  | input {e id v} : view e = some (.input id) → inputs id = some v → MeaningP inputs e v
  | value {e v} : view e = some (.value v) → MeaningP inputs e v
  | binary {e op a b va vb v} : view e = some (.binary op a b) →
      MeaningP inputs a va → MeaningP inputs b vb → op.run va vb = some v → MeaningP inputs e v
  | boolNot {e a b} : view e = some (.boolNot a) → MeaningP inputs a (.bool b) →
      MeaningP inputs e (.bool (!b))
  | mux {e kind c a b vc va vb v} : view e = some (.mux kind c a b) →
      MeaningP inputs c vc → MeaningP inputs a va → MeaningP inputs b vb →
      muxValue kind vc va vb = some v → MeaningP inputs e v
  | setw {e w w' a va v} : view e = some (.setw w w' a) →
      MeaningP inputs a va → setwValue w w' va = some v → MeaningP inputs e v
  | slice {e w start len a va v} : view e = some (.slice w start len a) →
      MeaningP inputs a va → sliceValue w start len va = some v → MeaningP inputs e v
  | concat {e m n a b va vb v} : view e = some (.concat m n a b) →
      MeaningP inputs a va → MeaningP inputs b vb → concatValue m n va vb = some v →
      MeaningP inputs e v
  | inst {e mn lvls pre args vs v} : view e = none → e.getAppFn = .const mn lvls →
      instSpineArgs e = pre ++ args → args.length = ChildPorts.ports mn →
      vs.length = args.length →
      (∀ i (ha : i < args.length) (hv : i < vs.length),
        MeaningP inputs (args[i]'ha) (vs[i]'hv)) →
      ChildSem.childSem mn vs = some v → MeaningP inputs e v

/-- The arguments an instance meaning reads are the compiler's. -/
theorem MeaningP.inst_args {e : Lean.Expr} {mn : Name} {pre args : List Lean.Expr}
    (hsp : instSpineArgs e = pre ++ args) (hports : args.length = ChildPorts.ports mn) :
    args = (instSpineArgs e).drop ((instSpineArgs e).length - ChildPorts.ports mn) :=
  (portArgs_eq hsp hports).symm

/-- A recorded expression has one source value (the cache-insertion
obligation, as `Meaning.deterministic`). The two readings of one call split
the same spine at the same port count, so they read the same arguments. -/
theorem MeaningP.deterministic {inputs e a b} (ha : MeaningP inputs e a)
    (hb : MeaningP inputs e b) : a = b := by
  induction ha generalizing b with
  | inst hview hfn hsp hports hlen hargs hsem ih =>
    cases hb with
    | inst hview' hfn' hsp' hports' hlen' hargs' hsem' =>
      have hc := Lean.Expr.const.inj (hfn.symm.trans hfn')
      obtain ⟨hmn, -⟩ := hc
      subst hmn
      have hargsEq := (List.append_inj' (hsp.symm.trans hsp') (hports.trans hports'.symm)).2
      subst hargsEq
      have hvs := List.ext_getElem (hlen.trans hlen'.symm) (fun i h1 h2 =>
        ih i (by rw [← hlen]; exact h1) h1 (hargs' i (by rw [← hlen]; exact h1) h2))
      subst hvs
      exact Option.some.inj (hsem.symm.trans hsem')
    | _ => simp_all
  | _ => cases hb <;> grind

/-- The child semantics is defined only at each callee's port count. -/
def ArityOK : Prop :=
  ∀ (mn : Name) (vs : List Value) (v : Value),
    ChildSem.childSem mn vs = some v → vs.length = ChildPorts.ports mn

/-- One leading argument is the prefix `[dom]`. -/
theorem MeaningP.inst_cons {inputs : FVarId → Option Value} {e : Lean.Expr} {mn : Name}
    {lvls : List Level} {dom : Lean.Expr} {args : List Lean.Expr} {vs : List Value} {v : Value}
    (hview : view e = none) (hfn : e.getAppFn = .const mn lvls)
    (hsp : instSpineArgs e = dom :: args) (hports : args.length = ChildPorts.ports mn)
    (hlen : vs.length = args.length)
    (hargs : ∀ i (ha : i < args.length) (hv : i < vs.length),
      MeaningP inputs (args[i]'ha) (vs[i]'hv))
    (hsem : ChildSem.childSem mn vs = some v) : MeaningP inputs e v :=
  .inst (pre := [dom]) hview hfn hsp hports hlen hargs hsem

/-- **Compatibility, part 1**: every old meaning is a new meaning, at the
same value. -/
theorem meaningP_of_meaning (hA : ArityOK) {inputs : FVarId → Option Value}
    {e : Lean.Expr} {v : Value} (h : Meaning inputs e v) : MeaningP inputs e v := by
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
    exact MeaningP.inst_cons hview hfn hsp (hlen.symm.trans (hA _ _ _ hsem)) hlen ih hsem

/-- **Compatibility, part 2 (the meaning is unchanged where the old one is
defined)**: on an expression with an old meaning `v`, the new meanings are
exactly `v`. -/
theorem meaningP_agree (hA : ArityOK) {inputs : FVarId → Option Value}
    {e : Lean.Expr} {v : Value} (h : Meaning inputs e v) (v' : Value) :
    MeaningP inputs e v' ↔ v' = v :=
  ⟨fun h' => MeaningP.deterministic h' (meaningP_of_meaning hA h),
   fun eq => eq ▸ meaningP_of_meaning hA h⟩

/-- **The finding, as a theorem**: under `ArityOK`, a call whose spine is
exactly its port arguments (no domain, no prefix: `pick sel x`) has NO old
meaning — `Meaning.inst` would read one argument fewer than the child
semantics is defined at. So every theorem with a `Meaning` / `LeafMeaning`
premise on such a leaf is vacuous for it (nothing false follows; nothing
follows). -/
theorem no_meaning_of_portsSpine (hA : ArityOK) {inputs : FVarId → Option Value}
    {e : Lean.Expr} {v : Value} {mn : Name} {lvls : List Level}
    (hview : view e = none) (hfn : e.getAppFn = .const mn lvls)
    (hports : (instSpineArgs e).length = ChildPorts.ports mn) :
    ¬ Meaning inputs e v := by
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

/-- A leaf's new meaning, with the child semantics and port counts explicit
(the twin of `Tools.ShippingHierTermSoundness.LeafMeaning`). -/
def LeafMeaningP (C : ChildSem) (P : ChildPorts) (inputs : FVarId → Option Value)
    (e : Lean.Expr) (v : Value) : Prop :=
  @MeaningP C P inputs e v

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

#print axioms Tools.ShippingInstanceMeaningP.MeaningP.deterministic
#print axioms Tools.ShippingInstanceMeaningP.meaningP_of_meaning
#print axioms Tools.ShippingInstanceMeaningP.meaningP_agree
#print axioms Tools.ShippingInstanceMeaningP.no_meaning_of_portsSpine
#print axioms Tools.ShippingInstanceMeaningP.instUncached_shapeE
#print axioms Tools.ShippingInstanceMeaningP.instUncached_shape_of_E
#print axioms Tools.ShippingInstanceMeaningP.instUncached_linkedE
