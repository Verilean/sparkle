import Tools.ShippingGateConeLeafRuns
import Tools.ShippingGateConeLeafContract
import Tools.ShippingChildTranslate
import Tools.ShippingWalkGrow
import Tools.ShippingHierTermSoundness

variable {tenv : Lean.Environment}

/-! # The cone at world level: `ContractW` (worker N, round 3)

WRITTEN, NOT BUILT.

The built cone composition (`fuel_contract_leaves`) is over `Contract`s, which
speak of EVERY `Returns` run of a translation, in any world: an instance
leaf's contract then needs the child of every run pinned
(`SubSynthDefinesAll`). Here the contract is indexed by the worlds of ONE
run:

* `ContractW L mF D rec … e v`: the frame and the semantic outcome of every
  returning run of `rec e …` that STARTS in an invariant world at depth `D`
  and ENDS in a world whose child cache is contained in `mF` (`SubMap`).
  `mF` will be the child cache at the end of the parent's translation: every
  child a leaf of the cone synthesised is THE entry of its callee there
  (`inst_leaf_runs`, entries are kept), so a repeated callee is one pair.
* `RunsC`: a `CompilerM` run with its worlds (the action is an ARGUMENT, so
  `split` sees an `if` / `match` of the action as the built `Returns`
  proofs do).
* `ContractW.ofContract` — a world-free `Contract` gives a `ContractW`
  (input binders, literals); `ContractW.zero` — fuel 0 throws.
* **`inst_leaf_contractW`** — the instance leaf, with NO pinned child and NO
  tag premise beyond the translator's own environment: the run's child `y`
  (a `RealChild`, `inst_leaf_runs`) is `mF`'s entry of the callee, and the
  child facts are asked of `mF`'s entry only (`KidFacts`); the second half is
  the built `armCont_leaf_contract`.
* the binary node at world level: `core_binary_eq`, `binary_returnsW`
  (the decomposition of the built `binary_returns`, with worlds),
  `binary_frameAt` / `binary_outcomeAt` (the text of the built
  `binary_frame` / `binary_outcome` over the operand runs' own facts,
  `ChildAt`), `binary_coreW`, **`binary_contractW`**.
* **`fuel_contractW`** — the fuel induction over the fragment `cfrag`
  (leaves, the three literals, `binary`); the leaves bring `ContractW`s at
  every fuel.
* `LeafK` / `InstLeafK` / `KidFacts` and **`leafK_contractW`**: a leaf is
  either a world-free leaf contract (`LeafContract`, e.g. an input binder) or
  a canonical call of a callee designated in the translator's environment
  whose arguments have world-free leaf contracts and whose `mF` entry has
  the child facts.

NOT covered (each is the same world-level walk as `binary_contractW`): the
other cone nodes (`compare`, `boolBinary`, `boolNot`, `boolEq`, `mux`,
`setw`, slices, concatenations, applicative forms) and instance calls whose
ARGUMENTS contain instance calls (`instArgs` at world level). -/
namespace Tools.ShippingGateParentRun
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTypedExprSoundness
open Tools.ShippingScalarSoundness Tools.ShippingBuilderSoundness
open Tools.ShippingCompareLoweringSoundness Tools.ShippingMuxRecursionSoundness
open Tools.ShippingMuxLoweringSoundness Tools.ShippingBoolLiteralSoundness
open Tools.ShippingBoolMuxSoundness Tools.ShippingEntrySoundness
open Tools.ShippingMuxTypeSoundness
open Tools.ShippingBindingsSoundness (visible)
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)
open Tools.ShippingUnifiedRecursion
open Tools.ShippingLinkCtx
open Tools.ShippingHierarchySoundness
open Tools.ShippingInstanceLeaf (ChildCorrect)
open Tools.ShippingInstanceEntrySoundness (instEN)
open Tools.ShippingChildInv (RefLaws InvV J KeepsC Res RealChild CacheInv childKeeps
  cacheLookupValidated_keepsC recordTranslation_keepsC makeWire_keepsC emitAssign_keepsC)
open Tools.ShippingCacheCoherentRun (SubMap sub_trans sub_refl)

set_option linter.unusedSectionVars false

variable {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State}
  {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}

/-! ## Runs of `CompilerM` actions, with their worlds -/

/-- `c` run from compiler state `ctx`, circuit state `s`, world `w`, in these
contexts and references, returns `p` in world `w'`. The action is an
argument: an `if` / `match` of the action is fully applied. -/
def RunsC {α : Type} (c : CompilerM α) (ctx : CompilerState) (s : CircuitState)
    (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State)
    (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State)
    (w : Void IO.RealWorld) (p : α × CircuitState) (w' : Void IO.RealWorld) : Prop :=
  RunsTo (c ctx s) mctx mref cctx cref w p w'

theorem RunsC.bind {α β : Type} {c : CompilerM α} {f : α → CompilerM β}
    {ctx : CompilerState} {s : CircuitState} {w : Void IO.RealWorld} {r : β × CircuitState}
    {w' : Void IO.RealWorld}
    (h : RunsC (c >>= f) ctx s mctx mref cctx cref w r w') :
    ∃ (a : α) (s1 : CircuitState) (w1 : Void IO.RealWorld),
      RunsC c ctx s mctx mref cctx cref w (a, s1) w1 ∧
      RunsC (f a) ctx s1 mctx mref cctx cref w1 r w' :=
  RunsTo.bindC h

theorem RunsC.pure {α : Type} {a : α} {ctx : CompilerState} {s : CircuitState}
    {w : Void IO.RealWorld} {r : α × CircuitState} {w' : Void IO.RealWorld}
    (h : RunsC (Pure.pure a : CompilerM α) ctx s mctx mref cctx cref w r w') :
    r = (a, s) ∧ w' = w :=
  Tools.ShippingChildInv.RunsTo.pure_world (a := (a, s)) h

theorem runsCReturns {α : Type} {c : CompilerM α} {ctx : CompilerState} {s : CircuitState}
    {w : Void IO.RealWorld} {a : α} {s' : CircuitState} {w' : Void IO.RealWorld}
    (h : RunsC c ctx s mctx mref cctx cref w (a, s') w') :
    Tools.ShippingTranslateSoundness.Returns c ctx s a s' :=
  ⟨mctx, mref, cctx, cref, w, w', h⟩

/-- **A returning run of an action that keeps the invariant at depth `D` for
every law witness**: the invariant, the depth, and every entry of the child
cache are kept (`WG.ofKeeps`). -/
theorem keepsW (L : RefLaws mref cref) {D : Nat} {α : Type} {c : CompilerM α}
    {ctx : CompilerState} {st : CircuitState} {w : Void IO.RealWorld}
    {p : α × CircuitState} {w' : Void IO.RealWorld}
    (hk : ∀ L' : RefLaws mref cref, KeepsC mctx mref cctx cref (J L' D) c)
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsC c ctx st mctx mref cctx cref w p w') :
    InvV L w' ∧ L.dval w' = D ∧ SubMap (L.val w) (L.val w') := by
  obtain ⟨h1, h2, h3, -⟩ := Tools.ShippingWalkGrow.WG.ofKeeps (mctx := mctx) (cctx := cctx)
    (L := L) (D := D) (ctx := ctx) (c := c) (P := fun _ => True)
    (fun L' st0 => hk L' ctx st0) st w p w' hw hd trivial hr
  exact ⟨h1, h2, h3⟩

/-- The recursive translator at any fuel, from an invariant world of positive
depth `D`. -/
theorem fuel_runsW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (k : Nat)
    {e : Lean.Expr} {hint : String} {top named : Bool} {ctx : CompilerState}
    {s : CircuitState} {w : Void IO.RealWorld} {p : String × CircuitState}
    {w' : Void IO.RealWorld}
    (hw : InvV L w) (hd : L.dval w = D)
    (hr : RunsC (translateFuelFix (translateStep tenv) k e hint top named) ctx s
      mctx mref cctx cref w p w') :
    InvV L w' ∧ L.dval w' = D ∧ SubMap (L.val w) (L.val w') :=
  keepsW L (fun L' => fuelRec_keepsC (tenv := tenv) L' D (childKeeps L' D (fun h => absurd h hD))
    k mctx cctx e hint top named) hw hd hr

/-! ## The world-indexed contract -/

/-- **The world-indexed contract** of `rec` on `e` with value `v`: every
returning run from an invariant world at depth `D` that ends in a world whose
child cache is contained in `mF` keeps the structural frame and has the
semantic outcome. -/
structure ContractW [LinkCtx] [ChildSem] (L : RefLaws mref cref)
    (mF : Std.HashMap Lean.Name Res) (D : Nat) (rec : TranslateFn) (ctx : CompilerState)
    (inputs : FVarId → Option Value) (we : WEnv) (mems : MEnv) (initial : Env)
    (e : Lean.Expr) (v : Value) : Prop where
  frame : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String) (top named : Bool)
    (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
    Lookup ctx inputs s → InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
    RunsC (rec e hint top named) ctx s mctx mref cctx cref w0 (w, t) w1 → Frame s t
  sem : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String) (top named : Bool)
    (s t : CircuitState) (w : String) (prior : Env) (w0 w1 : Void IO.RealWorld),
    Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
    InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
    RunsC (rec e hint top named) ctx s mctx mref cctx cref w0 (w, t) w1 →
    Outcome ctx inputs we mems initial prior s t w v

/-- The facts of ONE run of a child: what `binary_outcome` uses of `Child`. -/
structure ChildAt [LinkCtx] [ChildSem] (ctx : CompilerState) (inputs : FVarId → Option Value)
    (we : WEnv) (mems : MEnv) (initial : Env) (s t : CircuitState) (w : String) (v : Value) :
    Prop where
  frame : Lookup ctx inputs s → Frame s t
  sem : ∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
    Outcome ctx inputs we mems initial prior s t w v

/-- The child facts of `mF`'s entry `y` of the callee `mn` (`n` arguments,
value `v`), in the linked context of `children` and the child semantics `C`:
the premises of the built `armCont_leaf_contract` about the pair, the child
correctness written out (the text of `ChildCorrect`). -/
def KidFacts (children : String → Option (Sparkle.IR.AST.Module × WEnv)) (C : ChildSem)
    (mn : Lean.Name) (n : Nat) (v : Value) (y : Res) : Prop :=
  ∃ (cwe : WEnv) (outName : String) (wOut : Nat),
    y.2.modules = [] ∧
    (∀ p ∈ y.1.inputs, (p.name == "clk") = false ∧ (p.name == "rst") = false) ∧
    (y.1.inputs.map (·.name)).Nodup ∧
    y.1.outputs = [⟨outName, .bitVector wOut⟩] ∧
    (∀ p ∈ y.1.inputs, (outName == p.name) = false) ∧
    y.1.inputs.length = n ∧ v.kind.width = wOut ∧
    children y.1.name = some (y.1, cwe) ∧
    (∀ (mems : MEnv) (envIn : Env) (vs : List Value) (u : Value),
      @ChildSem.childSem C mn vs = some u →
      (∀ k (hk : k < y.1.inputs.length) (hk' : k < vs.length),
        envIn (y.1.inputs[k]'hk).name = (vs[k]'hk').toNat) →
      ∃ cres, evalAssigns cwe mems y.1.body envIn = some cres ∧ cres outName = u.toNat)

section generic
variable [LinkCtx] [ChildSem]

theorem ContractW.atRun {L : RefLaws mref cref} {mF : Std.HashMap Lean.Name Res} {D : Nat}
    {rec : TranslateFn} {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv}
    {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value}
    (c : ContractW L mF D rec ctx inputs we mems initial e v)
    {hint : String} {top named : Bool} {s t : CircuitState} {w : String}
    {w0 w1 : Void IO.RealWorld}
    (hw : InvV L w0) (hd : L.dval w0 = D) (hsub : SubMap (L.val w1) mF)
    (hr : RunsC (rec e hint top named) ctx s mctx mref cctx cref w0 (w, t) w1) :
    ChildAt ctx inputs we mems initial s t w v :=
  ⟨fun lookup => c.frame mctx cctx hint top named s t w w0 w1 lookup hw hd hsub hr,
    fun prior h widths => c.sem mctx cctx hint top named s t w prior w0 w1 h widths hw hd hsub hr⟩

/-- A world-free contract is a world-indexed one. -/
theorem ContractW.ofContract {L : RefLaws mref cref} {mF : Std.HashMap Lean.Name Res} {D : Nat}
    {rec : TranslateFn} {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv}
    {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value}
    (c : Contract rec ctx inputs we mems initial e v) :
    ContractW L mF D rec ctx inputs we mems initial e v :=
  ⟨fun _ _ hint top named s t w _ _ lookup _ _ _ hr =>
      c.frame hint top named s t w lookup (runsCReturns hr),
    fun _ _ hint top named s t w prior _ _ h widths _ _ _ hr =>
      c.sem hint top named s t w prior h widths (runsCReturns hr)⟩

/-- At fuel 0 the translator throws. -/
theorem ContractW.zero {L : RefLaws mref cref} {mF : Std.HashMap Lean.Name Res} {D : Nat}
    {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv}
    {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value} :
    ContractW L mF D (translateFuelFix (translateStep tenv) 0) ctx inputs we mems initial e v :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr => (Returns.throw (runsCReturns hr)).elim,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr => (Returns.throw (runsCReturns hr)).elim⟩

/-! ## The binary node at world level -/

/-- The core on a canonical binary node IS the binary lowering. -/
theorem core_binary_eq {rec : TranslateFn} {e : Lean.Expr} {m : Lean.Name} {us : List Level}
    {op : Operator} {n : Nat} {hint : String} {top named : Bool}
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n) :
    translateCore rec e hint top named =
      (translateCanonicalSignalBinary rec e op e.getAppArgs true true hint named >>=
        fun w => Pure.pure (some w)) := by
  have ne : m ≠ ``Sparkle.Core.Signal.Signal.pure := by
    intro eq; subst m; simp [signalBinOpOf] at hop
  unfold translateCore
  split
  · simp [Lean.Expr.getAppFn] at fn
  · rw [fn]
    simp only [beq_eq_false_iff_ne.mpr ne, Bool.false_eq_true, if_false, hop, kinds, width]
    try rfl

/-- **The binary lowering, with its worlds** (the decomposition of the built
`binary_returns`). -/
theorem binary_returnsW {rec : TranslateFn} {e : Lean.Expr} {op : Operator}
    {args : Array Lean.Expr} {hint : String} {named : Bool} {ctx : CompilerState}
    {s t : CircuitState} {w : String} {n : Nat} {w0 w1 : Void IO.RealWorld}
    (width : canonicalSignalBitVecWidth args = some n)
    (hr : RunsC (translateCanonicalSignalBinary rec e op args true true hint named) ctx s
      mctx mref cctx cref w0 (w, t) w1) :
    ∃ (sa sb sc : CircuitState) (a b : String) (wm wa wb : Void IO.RealWorld),
      w = (CircuitM.makeWire hint (.bitVector n) named s).1 ∧
      sa = (CircuitM.makeWire hint (.bitVector n) named s).2 ∧
      RunsC (CompilerM.makeWire hint (.bitVector n) named) ctx s mctx mref cctx cref w0 (w, sa) wm ∧
      RunsC (rec args[args.size - 2]! "op_a" false false) ctx sa mctx mref cctx cref wm (a, sb) wa ∧
      RunsC (rec args[args.size - 1]! "op_b" false false) ctx sb mctx mref cctx cref wa (b, sc) wb ∧
      RunsC (CompilerM.emitAssign w (.op op [.ref a, .ref b])) ctx sc mctx mref cctx cref
        wb ((), t) w1 ∧
      t = (CircuitM.emitAssign w (.op op [.ref a, .ref b]) sc).2 := by
  unfold translateCanonicalSignalBinary at hr
  simp only [width] at hr
  obtain ⟨ty, sq, wq, query, rest⟩ := RunsC.bind hr
  obtain ⟨hq, hwq⟩ := RunsC.pure query
  obtain ⟨hty, hsq⟩ := Prod.mk.inj hq
  subst hty hsq hwq
  obtain ⟨r, sa, wm, mk, rest⟩ := RunsC.bind rest
  obtain ⟨hw, hsa⟩ := makeWire_returns (runsCReturns mk)
  obtain ⟨a, sb, wa, ra, rest⟩ := RunsC.bind rest
  obtain ⟨b, sc, wb, rb, rest⟩ := RunsC.bind rest
  obtain ⟨u, sd, wd, emit, rest⟩ := RunsC.bind rest
  obtain ⟨hp, hw1⟩ := RunsC.pure rest
  obtain ⟨hrw, ht⟩ := Prod.mk.inj hp
  subst hrw ht hw1
  cases u
  exact ⟨sa, sb, sc, a, b, wm, wa, wb, hw, hsa, mk, ra, rb, emit,
    emitAssign_returns (runsCReturns emit)⟩

/-- The structural half over the operand runs' own facts (the text of the
built `binary_frame`). -/
theorem binary_frameAt {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv}
    {mems : MEnv} {initial : Env} {s sa sb sc t : CircuitState} {hint : String} {named : Bool}
    {w a b : String} {n : Nat} {va vb : Value}
    (op : Binary) (lookup : Lookup ctx inputs s)
    (hw : w = (CircuitM.makeWire hint (.bitVector n) named s).1)
    (hsa : sa = (CircuitM.makeWire hint (.bitVector n) named s).2)
    (ca : ChildAt ctx inputs we mems initial sa sb a va)
    (cb : ChildAt ctx inputs we mems initial sb sc b vb)
    (ht : t = (CircuitM.emitAssign w (.op op.operator [.ref a, .ref b]) sc).2) :
    Frame s t ∧ s.usedNames.contains w = false := by
  have fa : Frame s sa := by rw [hsa]; exact Frame.makeWire s hint n named
  have fb := ca.frame (lookup.transfer fa)
  have fc := cb.frame ((lookup.transfer fa).transfer fb)
  have fd : Frame sc t := by rw [ht]; exact Frame.emitAssign sc w _ (by cases op <;> rfl)
  refine ⟨((fa.trans fb).trans fc).trans fd, ?_⟩
  rw [hw]; exact (CircuitM.makeWire_spec hint (.bitVector n) named s).1

/-- The semantic half over the operand runs' own facts (the text of the
built `binary_outcome`). -/
theorem binary_outcomeAt {ctx : CompilerState} {inputs : FVarId → Option Value} {we : WEnv}
    {mems : MEnv} {initial : Env} {s sa sb sc t : CircuitState} {prior : Env} {hint : String}
    {named : Bool} {w a b : String} {n : Nat}
    (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (h : Inv ctx inputs we mems initial s prior)
    (hw : w = (CircuitM.makeWire hint (.bitVector n) named s).1)
    (hsa : sa = (CircuitM.makeWire hint (.bitVector n) named s).2)
    (ca : ChildAt ctx inputs we mems initial sa sb a (.bits n x))
    (cb : ChildAt ctx inputs we mems initial sb sc b (.bits n y))
    (ht : t = (CircuitM.emitAssign w (.op op.operator [.ref a, .ref b]) sc).2)
    (widths : ScalarWidthsAgree we t) :
    Frame s t ∧ Outcome ctx inputs we mems initial prior s t w (.bits n (op.apply x y)) := by
  have lookup := Lookup.ofInputs h.inputs
  have alloc := CircuitM.makeWire_spec hint (.bitVector n) named s
  have fresh : s.usedNames.contains w = false := by rw [hw]; exact alloc.1
  have usedA : sa.usedNames.contains w = true := by rw [hsa, alloc.2.1, hw]; simp
  have fa : Frame s sa := by rw [hsa]; exact Frame.makeWire s hint n named
  have fb := ca.frame (lookup.transfer fa)
  have fc := cb.frame ((lookup.transfer fa).transfer fb)
  have fd : Frame sc t := by rw [ht]; exact Frame.emitAssign sc w _ (by cases op <;> rfl)
  have all := ((fa.trans fb).trans fc).trans fd
  have ia : Inv ctx inputs we mems initial sa prior := by
    rw [hsa]; exact h.allocate hint (.bitVector n) named
  have wa := ca.sem prior ia ((fc.decls.trans fd.decls).widths widths)
  obtain ⟨vb, ib, av, aframe⟩ := wa.execution
  have wb := cb.sem vb ib (fd.decls.widths widths)
  obtain ⟨vc, ic, bv, bframe⟩ := wb.execution
  have av' : vc a = x.toNat := (bframe a wa.used).trans av
  have resultWidth : we w = n := by
    apply widths ({name := w, ty := .bitVector n} : Port)
    apply fd.decls; apply fc.decls; apply fb.decls
    rw [hsa, alloc.2.2.2, hw]; simp
  have sameBindings : sc.sourceBindings = s.sourceBindings :=
    fc.bindings.trans (fb.bindings.trans fa.bindings)
  have oldRecord : ∀ ex, sc.translateRecord.get? w = some ex →
      s.translateRecord.get? w = some ex := by
    intro ex he
    have old := fb.record_reserved usedA (fc.record_reserved (fb.used w usedA) he)
    rw [hsa, CircuitM.makeWire_translateRecord] at old
    exact old
  have inputSafe : ∀ id u, inputs id = some u → visible ctx sc.sourceBindings id ≠ some w := by
    intro id u hi bound
    rw [sameBindings] at bound
    obtain ⟨z, hz, hu, _, _⟩ := h.inputs.lookup id u hi
    have eq : z = w := Option.some.inj (hz.symm.trans bound)
    subst z; simp [fresh] at hu
  have recordSafe : ∀ ex u, sc.translateRecord.get? w = some ex → ¬ Meaning inputs ex u := by
    intro ex u he meaning
    have hu := (h.records w ex (oldRecord ex he) u meaning).1
    simp [fresh] at hu
  have typed : TypedExpr we (.op op.operator [.ref a, .ref b]) (we w) := by
    rw [resultWidth]
    have wa' : we a = n := wa.width
    have wb' : we b = n := wb.width
    exact .bin op (wa' ▸ TypedExpr.ref (we := we) a (by rw [wa']; exact hn))
      (wb' ▸ TypedExpr.ref (we := we) b (by rw [wb']; exact hn)) (by cases op <;> rfl)
  have bv' : vc b = y.toNat := bv
  have rhs := Binary.rhs_correct op we vc a b x y wa.width wb.width av' bv'
  have final := ic.emit_reserved inputSafe recordSafe typed rhs
  rw [← ht] at final
  refine ⟨all, fd.used w (fc.used w (fb.used w usedA)), resultWidth, all.used,
    write vc w (op.apply x y).toNat, final, ?_, ?_⟩
  · simp [write]
  · intro z hz
    have ne : z ≠ w := by intro eq; subst z; simp [fresh] at hz
    simp only [write, ne, if_false]
    exact (bframe z (fb.used z (fa.used z hz))).trans (aframe z (fa.used z hz))

/-- **The core and the record of a binary node, at world level**: from an
invariant world of positive depth, ending in a world whose cache is in `mF`. -/
theorem binary_coreW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {e : Lean.Expr} {m : Lean.Name} {us : List Level}
    {n : Nat} {hint : String} {top named cacheable : Bool} {s t : CircuitState} {w : String}
    {w0 w1 : Void IO.RealWorld} {K : Option String → CompilerM String}
    (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (meaning : Meaning inputs e (.bits n (op.apply x y)))
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      e.getAppArgs[e.getAppArgs.size - 2]! (.bits n x))
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      e.getAppArgs[e.getAppArgs.size - 1]! (.bits n y))
    (hk : ∀ z, K (some z) = (recordTranslation e z cacheable >>= fun _ => Pure.pure z))
    (hw0 : InvV L w0) (hd0 : L.dval w0 = D) (hsub : SubMap (L.val w1) mF)
    (hr : RunsC (translateCore (translateFuelFix (translateStep tenv) fuel) e hint top named >>= K)
      ctx s mctx mref cctx cref w0 (w, t) w1) :
    (Lookup ctx inputs s → Frame s t) ∧
      (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
        Outcome ctx inputs we mems initial prior s t w (.bits n (op.apply x y))) := by
  obtain ⟨r, sm, wc, core, rest⟩ := RunsC.bind hr
  rw [core_binary_eq fn hop kinds width] at core
  obtain ⟨z, sm', wz, lower, back⟩ := RunsC.bind core
  obtain ⟨hp, hwz⟩ := RunsC.pure back
  obtain ⟨hrz, hsm⟩ := Prod.mk.inj hp
  subst hrz hsm hwz
  rw [hk] at rest
  obtain ⟨u, sr, wr, record, fin⟩ := RunsC.bind rest
  obtain ⟨hp2, hw1⟩ := RunsC.pure fin
  obtain ⟨hwz', ht'⟩ := Prod.mk.inj hp2
  subst hwz' ht' hw1
  obtain ⟨sa, sb, sc, a, b, wm, wa, wb, hw, hsa, rmk, ra, rb, remit, ht⟩ :=
    binary_returnsW width lower
  -- the worlds: makeWire, operand a, operand b, the assign, the record
  obtain ⟨hwm, hdm, -⟩ :=
    keepsW L (fun L' => makeWire_keepsC L' D hint (.bitVector n) named) hw0 hd0 rmk
  obtain ⟨hwa, hda, hsab⟩ := fuel_runsW (tenv := tenv) L hD fuel hwm hdm ra
  obtain ⟨hwb, hdb, hsbc⟩ := fuel_runsW (tenv := tenv) L hD fuel hwa hda rb
  obtain ⟨hwc, hdc, hscd⟩ :=
    keepsW L (fun L' => emitAssign_keepsC L' D w (.op op.operator [.ref a, .ref b])) hwb hdb remit
  obtain ⟨-, -, hsd⟩ :=
    keepsW L (fun L' => recordTranslation_keepsC L' D e w cacheable) hwc hdc record
  have subB : SubMap (L.val wb) mF := sub_trans hscd (sub_trans hsd hsub)
  have subA : SubMap (L.val wa) mF := sub_trans hsbc subB
  have caAt := ca.atRun hwm hdm subA ra
  have cbAt := cb.atRun hwa hda subB rb
  have recordR : Returns (recordTranslation e w cacheable) ctx sm u t := runsCReturns record
  have hs := recordTranslation_returns recordR
  refine ⟨fun lookup => ?_, fun prior h widths => ?_⟩
  · obtain ⟨growth, fresh⟩ := binary_frameAt op lookup hw hsa caAt cbAt ht
    exact growth.record_new fresh recordR
  · have wm' : ScalarWidthsAgree we sm := by
      intro p hp; apply widths p; rw [hs]; exact hp
    obtain ⟨-, step⟩ := binary_outcomeAt op x y hn h hw hsa caAt cbAt ht wm'
    obtain ⟨result, inv, val, frame⟩ := step.execution
    refine ⟨?_, step.width, ?_, result,
      inv.record meaning step.used val step.width recordR, val, frame⟩
    · rw [hs]; exact step.used
    · rw [hs]; exact step.grows

/-- **The world-indexed contract of a canonical binary node**, from those of
its operands. -/
theorem binary_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {e : Lean.Expr} {m : Lean.Name} {us : List Level}
    {n : Nat}
    (op : Binary) (x y : BitVec n) (hn : 0 < n)
    (fn : e.getAppFn = .const m us) (hop : signalBinOpOf m = some op.operator)
    (kinds : canonicalSignalBinKinds m e.getAppArgs = some (true, true))
    (width : canonicalSignalBitVecWidth e.getAppArgs = some n)
    (meaning : Meaning inputs e (.bits n (op.apply x y)))
    (ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      e.getAppArgs[e.getAppArgs.size - 2]! (.bits n x))
    (cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
      e.getAppArgs[e.getAppArgs.size - 1]! (.bits n y)) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial e
      (.bits n (op.apply x y)) := by
  have nf := isFVar_false_of_const fn
  have step : ∀ (mctx : Lean.Meta.Context) (cctx : Lean.Core.Context) (hint : String)
      (top named : Bool) (s t : CircuitState) (w : String) (w0 w1 : Void IO.RealWorld),
      InvV L w0 → L.dval w0 = D → SubMap (L.val w1) mF →
      RunsC (translateFuelFix (translateStep tenv) (fuel + 1) e hint top named) ctx s
        mctx mref cctx cref w0 (w, t) w1 →
      (Lookup ctx inputs s → Frame s t) ∧
        (∀ prior, Inv ctx inputs we mems initial s prior → ScalarWidthsAgree we t →
          Outcome ctx inputs we mems initial prior s t w (.bits n (op.apply x y))) := by
    intro mctx cctx hint top named s t w w0 w1 hw0 hd0 hsub hr
    change RunsC (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel) e hint top named) ctx s
      mctx mref cctx cref w0 (w, t) w1 at hr
    unfold translateStepWith at hr
    dsimp only at hr
    split at hr
    · obtain ⟨hit, sh, w2, rh, hr2⟩ := RunsC.bind hr
      have rhR := runsCReturns rh
      have hs := (cacheLookupValidated_returns rhR).1
      subst hs
      obtain ⟨hw2, hd2, -⟩ :=
        keepsW L (fun L' => cacheLookupValidated_keepsC L' D e) hw0 hd0 rh
      split at hr2
      · obtain ⟨hp, -⟩ := RunsC.pure hr2
        obtain ⟨hw', ht'⟩ := Prod.mk.inj hp
        subst hw' ht'
        exact ⟨fun _ => Frame.refl _, fun prior h _ => hit_outcome h meaning rhR⟩
      · refine binary_coreW (cacheable := !named && !e.isFVar && !top) L hD fuel op x y hn
          fn hop kinds width meaning ca cb ?_ hw2 hd2 hsub hr2
        intro z; simp only [nf, Bool.false_eq_true, if_false]
    · refine binary_coreW (cacheable := !named && !e.isFVar && !top) L hD fuel op x y hn
        fn hop kinds width meaning ca cb ?_ hw0 hd0 hsub hr
      intro z; simp only [nf, Bool.false_eq_true, if_false]
  exact ⟨fun mctx cctx hint top named s t w w0 w1 lookup hw hd hsub hr =>
      (step mctx cctx hint top named s t w w0 w1 hw hd hsub hr).1 lookup,
    fun mctx cctx hint top named s t w prior w0 w1 h widths hw hd hsub hr =>
      (step mctx cctx hint top named s t w w0 w1 hw hd hsub hr).2 prior h widths⟩

/-! ## The fuel induction over the fragment -/

/-- The cone nodes walked at world level: leaves, the three literals, the
canonical binary operators. A term outside the fragment is not claimed
anything about. -/
def cfrag : {s : SType} → Term s → Bool
  | _, .boolInput _ => true
  | _, .bitsInput _ _ => true
  | _, .boolLit _ => true
  | _, .bitsLit _ _ => true
  | _, .bitsNum _ _ => true
  | _, .binary _ a b => cfrag a && cfrag b
  | _, _ => false

/-- **The fuel induction at world level** (the text of the built
`fuel_contract_leaves`, on the fragment): every leaf brings a world-indexed
contract at every fuel. -/
theorem fuel_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    (mF : Std.HashMap Lean.Name Res) {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env} {dom : Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    {bE vE : Nat → Lean.Expr} {bools : Nat → Bool} {bits : (j : Nat) → (w : Nat) → BitVec w}
    (hb : ∀ j, j < kb → Meaning inputs (bE j) (.bool (bools j)))
    (hv : ∀ j, j < kv → Meaning inputs (vE j) (.bits (vw j) (bits j (vw j))))
    (hbC : ∀ j, j < kb → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (bE j) (.bool (bools j)))
    (hvC : ∀ j, j < kv → ∀ fuel, ContractW L mF D (translateFuelFix (translateStep tenv) fuel)
      ctx inputs we mems initial (vE j) (.bits (vw j) (bits j (vw j)))) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw → cfrag e = true →
      ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
        (quote dom bE vE e) (pack s (eval bools bits e)) := by
  induction fuel with
  | zero =>
    intro s e _ _
    exact ContractW.zero
  | succ fuel ih =>
    intro s e he hf
    change ContractW L mF D (translateStepWith (translateFallback tenv)
      (translateFuelFix (translateStep tenv) fuel)) _ _ _ _ _ _ _
    cases e with
    | boolInput j => exact hbC j he (fuel + 1)
    | bitsInput w j =>
      obtain ⟨hj, hw, hpos⟩ := he
      cases hw
      exact hvC j hj (fuel + 1)
    | boolLit b =>
      exact ContractW.ofContract (rec := translateStepWith (translateFallback tenv)
        (translateFuelFix (translateStep tenv) fuel)) (bool_literal_contract b)
    | bitsLit w v =>
      obtain ⟨hval, hpos⟩ := he
      exact ContractW.ofContract (rec := translateStepWith (translateFallback tenv)
        (translateFuelFix (translateStep tenv) fuel)) (bits_literal_contract hpos hval)
    | bitsNum w v =>
      obtain ⟨hval, hpos⟩ := he
      exact ContractW.ofContract (rec := translateStepWith (translateFallback tenv)
        (translateFuelFix (translateStep tenv) fuel)) (num_literal_contract hpos hval)
    | binary op a b =>
      rename_i w
      obtain ⟨ha, hb'⟩ := he
      simp only [cfrag, Bool.and_eq_true] at hf
      have hn : 0 < w := a.wf_pos ha
      have ck := op_checks op dom (quote dom bE vE a) (quote dom bE vE b) w
      have ca : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems
          initial
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 2]!)
          (.bits w (eval bools bits a)) := by
        rw [ck.2.2.2.2.1]; exact ih a ha hf.1
      have cb : ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems
          initial
          ((binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs[(binE dom w op (quote dom bE vE a)
            (quote dom bE vE b)).getAppArgs.size - 1]!)
          (.bits w (eval bools bits b)) := by
        rw [ck.2.2.2.2.2.1]; exact ih b hb' hf.2
      exact binary_contractW L hD fuel op _ _ hn ck.1 ck.2.1 ck.2.2.1 ck.2.2.2.1
        (meaning_quote_leaves hb hv (.binary op a b) ⟨ha, hb'⟩) ca cb
    | _ => simp [cfrag] at hf

end generic

/-! ## The instance leaf at world level -/

section inst
variable [HierCtx] [ChildSem]

/-- **`inst_leaf_contractW`**: a canonical call of a callee designated in the
translator's environment, whose arguments have world-free contracts: a run at
fuel `fuel + 1` from an invariant world of positive depth, ending in a world
whose cache is in `mF`, synthesised the callee's child `y` (a `RealChild`)
which is `mF`'s entry; the child facts are asked of `mF`'s entry only. No
pinned child, no tag premise beyond the translator's environment. -/
theorem inst_leaf_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (fuel : Nat)
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {we : WEnv} {mems : MEnv} {initial : Env}
    {mn : Lean.Name} {lvls : List Level} {dom : Lean.Expr} {argsE : List Lean.Expr}
    {vs : List Value} {v : Value}
    (hpure : (mn == ``Sparkle.Core.Signal.Signal.pure) = false)
    (hbin : signalBinOpOf mn = none)
    (hkind : fallbackKind (instEN mn lvls dom argsE) = .other)
    (htag : Sparkle.Compiler.isHardwareModule tenv mn = true)
    (hlenV : argsE.length = vs.length)
    (hargs : ∀ k (hk : k < argsE.length) (hk' : k < vs.length),
      Contract (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial
        (argsE[k]'hk) (vs[k]'hk'))
    (meaning : Meaning inputs (instEN mn lvls dom argsE) v)
    (hsem : ChildSem.childSem mn vs = some v)
    (hkid : ∀ y : Res, mF.get? mn = some y →
      KidFacts HierCtx.children (inferInstance : ChildSem) mn argsE.length v y) :
    ContractW L mF D (translateFuelFix (translateStep tenv) (fuel + 1)) ctx inputs we mems initial
      (instEN mn lvls dom argsE) v := by
  constructor
  · intro mctx cctx hint top named s t w w0 w1 lookup hw hd hsub hr
    obtain ⟨y, -, hget, -, -, -, ret⟩ :=
      inst_leaf_runs (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
    obtain ⟨cwe, outName, wOut, hdc, hnoclk, hnodup, houts, houtFresh, hlen, hwidth, hchild,
      hcorrect⟩ := hkid y (hsub mn y hget)
    exact (armCont_leaf_contract hdc hnoclk hnodup houts houtFresh hlen hlenV hargs meaning hsem
      hwidth hchild hcorrect).frame hint top named s t w lookup ret
  · intro mctx cctx hint top named s t w prior w0 w1 h widths hw hd hsub hr
    obtain ⟨y, -, hget, -, -, -, ret⟩ :=
      inst_leaf_runs (tenv := tenv) L hD fuel hpure hbin hkind htag hw hd hr
    obtain ⟨cwe, outName, wOut, hdc, hnoclk, hnodup, houts, houtFresh, hlen, hwidth, hchild,
      hcorrect⟩ := hkid y (hsub mn y hget)
    exact (armCont_leaf_contract hdc hnoclk hnodup houts houtFresh hlen hlenV hargs meaning hsem
      hwidth hchild hcorrect).sem hint top named s t w prior h widths ret

end inst

/-! ## The leaves of a cone -/

/-- An instance leaf whose child is read off `mF`, in the linked context of
`children` and the child semantics `C`: a canonical call (none of the core /
fallback shapes) of a callee designated in `tenv`, its arguments with
world-free leaf contracts and values `vs`, the child's source function on
them is `v`, and `mF`'s entry of the callee has the child facts. -/
def InstLeafK (tenv : Lean.Environment) (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (C : ChildSem) (mF : Std.HashMap Lean.Name Res) (ctx : CompilerState)
    (inputs : FVarId → Option Value) (mems : MEnv) (initial : Env) (e : Lean.Expr) (v : Value) :
    Prop :=
  ∃ (mn : Lean.Name) (lvls : List Level) (dom : Lean.Expr) (argsE : List Lean.Expr)
    (vs : List Value),
    e = instEN mn lvls dom argsE ∧
    (mn == ``Sparkle.Core.Signal.Signal.pure) = false ∧
    signalBinOpOf mn = none ∧
    fallbackKind (instEN mn lvls dom argsE) = .other ∧
    Sparkle.Compiler.isHardwareModule tenv mn = true ∧
    argsE.length = vs.length ∧
    (∀ k (hk : k < argsE.length) (hk' : k < vs.length),
      Tools.ShippingHierTermSoundness.LeafContract tenv children C ctx inputs mems initial
        (argsE[k]'hk) (vs[k]'hk')) ∧
    @ChildSem.childSem C mn vs = some v ∧
    ∀ y : Res, mF.get? mn = some y → KidFacts children C mn argsE.length v y

/-- A leaf of a cone: a world-free leaf contract (an input binder, …) or an
instance leaf read off `mF`. -/
def LeafK (tenv : Lean.Environment) (children : String → Option (Sparkle.IR.AST.Module × WEnv))
    (C : ChildSem) (mF : Std.HashMap Lean.Name Res) (ctx : CompilerState)
    (inputs : FVarId → Option Value) (mems : MEnv) (initial : Env) (e : Lean.Expr) (v : Value) :
    Prop :=
  Tools.ShippingHierTermSoundness.LeafContract tenv children C ctx inputs mems initial e v ∨
    InstLeafK tenv children C mF ctx inputs mems initial e v

/-- **A leaf's world-indexed contract at every fuel**, in the linked context of
`children`. -/
theorem leafK_contractW (L : RefLaws mref cref) {D : Nat} (hD : D ≠ 0) (we : WEnv)
    {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {C : ChildSem}
    {mF : Std.HashMap Lean.Name Res} {ctx : CompilerState} {inputs : FVarId → Option Value}
    {mems : MEnv} {initial : Env} {e : Lean.Expr} {v : Value}
    (h : LeafK tenv children C mF ctx inputs mems initial e v)
    (hm : Tools.ShippingHierTermSoundness.LeafMeaning C inputs e v) (fuel : Nat) :
    letI : HierCtx := hierLink children
    letI : ChildSem := C
    ContractW L mF D (translateFuelFix (translateStep tenv) fuel) ctx inputs we mems initial e v := by
  letI : HierCtx := hierLink children
  letI : ChildSem := C
  rcases h with hc | ⟨mn, lvls, dom, argsE, vs, he, hpure, hbin, hkind, htag, hlenV, hargs, hsem,
    hkid⟩
  · exact ContractW.ofContract (hc we fuel)
  · subst he
    cases fuel with
    | zero => exact ContractW.zero
    | succ fuel =>
      exact inst_leaf_contractW L hD fuel hpure hbin hkind htag hlenV
        (fun k hk hk' => hargs k hk hk' we fuel) hm hsem hkid

end Tools.ShippingGateParentRun
