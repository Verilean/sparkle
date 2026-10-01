import Tools.ShippingUnifiedExecutionSoundness

/-! # S4: one register over the unified combinational domain

The canonical polymorphic-domain `Signal.register initLit input` root now has
a total lowering (`translateRegisterUncachedWith`) and a gate disjunct
(`unifiedRegisterRoot`). This module proves the compiled module's CYCLE
behaviour: each cycle's elaboration computes the register input from the
unified combinational contract, the output port reads the register's current
state, and the register update is exactly the source `Signal.register`
recurrence, with reset held low (the source has no reset primitive — the only
initialization is the t = 0 initial value, which the RTL register declares).

Scope: the raw synthesized module of `synthesizeCombinationalCore`; the
sequential post-processing passes (`dropZeroWidthModule`, and in particular
the UNVALIDATED sequential `mergeDuplicatesRaw`) are separate work. -/
namespace Tools.ShippingRegisterSoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedRecursion Tools.ShippingUnifiedProtection
open Tools.ShippingUnifiedEntrySoundness Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingTypedExprSoundness Tools.ShippingScalarSoundness
open Tools.ShippingBoolLiteralSoundness
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMixedInputSoundness (empty_layout)
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedBinarySoundness (Frame ScalarWires)
open Tools.ShippingMixedInvariant (Separate)
open Tools.ShippingTranslationOrder
open Tools.ShippingEntrySoundness Tools.ShippingMuxTypeSoundness
open Tools.ShippingBoolSourceSoundness

/-! ## The quoted root form -/

/-- `Signal.register (BitVec.ofNat w v) a`, exactly as the library call
elaborates over a polymorphic domain. -/
def registerE (dom : Lean.Expr) (w v : Nat) (a : Lean.Expr) : Lean.Expr :=
  mkApp4 (.const ``Sparkle.Core.Signal.Signal.register [.zero]) dom (bitVecE w)
    (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v)) a

theorem canonicalRegister?_registerE {dom a : Lean.Expr} {w v : Nat}
    (hdom : (dom.isFVar || dom.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w) :
    canonicalRegister? (registerE dom w v a) = some (w, v, a) := by
  have hlit := litValue_natE w v hv
  simp only [mkApp2, mkAppB, mkApp] at hlit
  simp only [registerE, mkApp4, mkApp2, mkAppB, mkApp, bitVecE, canonicalRegister?,
    hdom, if_true, canonicalNatLitValue?_natE, hlit]
  simp [hw]

theorem instFVars_registerE (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr)
    (w v : Nat) (a : Lean.Expr) :
    instFVars xs d (registerE dom w v a) =
      registerE (instFVars xs d dom) w v (instFVars xs d a) := rfl

/-! ## Gate acceptance -/

theorem unifiedRegisterRoot_registerE {kinds : Array MixedGateBinder} {dom a : Lean.Expr}
    {w v : Nat} (hdom : (dom.isFVar || dom.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (body : unifiedGateBitsBody kinds w a = true) :
    unifiedRegisterRoot kinds (registerE dom w v a) = true := by
  unfold unifiedRegisterRoot
  rw [canonicalRegister?_registerE hdom hw hv]
  simp [hw, body]

/-- Once the real declaration has been peeled to a register root over a quoted
unified source, the shipping gate accepts it. -/
theorem register_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {w v : Nat} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {e : Term (.bits w)}
    (peel : mixedGatePeel d.value = some (bs, registerE dom w v
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e)))
    (hdom : (dom.isFVar || dom.isBVar) = true) (hv : v < 2 ^ w)
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∀ isInst, mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, registerE dom w v
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e)) := by
  intro isInst
  have body : unifiedGateBitsBody (bs.map Prod.snd).toArray w
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) = true :=
    unified_quote_accepted
      (fun j hj => (hb j hj).elim fun name pos => input_bool_accepted pos)
      (fun j hj => (hvp j hj).elim fun name pos => input_bits_accepted pos) e he
  have root := unifiedRegisterRoot_registerE hdom (e.wf_pos he) hv body
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, Bool.or_true, Bool.true_or, if_true]

/-! ## The register emitter, lifted -/

theorem emitRegisterC_spec (hint clk rst : String) (input : Sparkle.IR.AST.Expr) (v : Nat)
    (ty : Sparkle.IR.Type.HWType) (named : Bool) (kind : Sparkle.IR.Type.ResetKind)
    (s : CircuitState) :
    (CircuitM.emitRegister hint clk rst input v ty named kind s).1 =
      (CircuitM.makeWire hint ty named s).1 ∧
    (CircuitM.emitRegister hint clk rst input v ty named kind s).2 =
      { (CircuitM.makeWire hint ty named s).2 with
        module := (CircuitM.makeWire hint ty named s).2.module.addStmt
          (.register (CircuitM.makeWire hint ty named s).1 clk (rst, kind) input v) } := by
  constructor <;> rfl

/-- The compiler's `emitRegister` is the builder's; the width-cache write does
not touch the builder state (same shape as `makeWire_returns`). -/
theorem emitRegister_returns {hint clk rst : String} {input : Sparkle.IR.AST.Expr}
    {v : Nat} {ty : Sparkle.IR.Type.HWType} {named : Bool}
    {ctx : CompilerState} {s s' : CircuitState} {w : String}
    (h : Returns (CompilerM.emitRegister hint clk rst input v ty (named := named)) ctx s w s') :
    w = (CircuitM.emitRegister hint clk rst input v ty named .asynchronous s).1 ∧
    s' = (CircuitM.emitRegister hint clk rst input v ty named .asynchronous s).2 := by
  unfold CompilerM.emitRegister at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  subst hcs hs1
  split at k1
  rename_i name cs' hmk
  obtain ⟨u, s2, hset, k2⟩ := Returns.bind k1
  have hs2 : s2 = cs' := Returns.set hset
  have goal : w = name ∧ s' = s2 := by
    split at k2
    · obtain ⟨u2, s3, hlift, k3⟩ := Returns.bind k2
      have h3 : s3 = s2 := Returns.liftMetaM hlift
      obtain ⟨hw, hs'⟩ := Returns.pure k3
      exact ⟨hw, hs'.trans h3⟩
    · exact Returns.pure k2
  rw [hmk]; exact ⟨goal.1, goal.2.trans hs2⟩

/-! ## Step rewrites for the root form -/

set_option maxHeartbeats 1000000 in
theorem registerUncached_registerE (rec : TranslateFn) (dom ae : Lean.Expr) (w v : Nat)
    (hint : String) (top named : Bool) :
    translateRegisterUncachedWith rec w v (registerE dom w v ae) hint top named =
      (do
        let cw ← rec ae "reg_in" false false
        CompilerM.emitRegister hint "clk" "rst" (.ref cw) v (.bitVector w)
          (named := named)) := rfl

set_option maxHeartbeats 1000000 in
theorem register_step (rec : TranslateFn) (dom ae : Lean.Expr) (w v : Nat)
    (hdom : (dom.isFVar || dom.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (registerE dom w v ae) hint top named =
      translateControlCachedWith (translateRegisterUncachedWith rec w v)
        (registerE dom w v ae) hint top named := by
  have shape : translateCoreShape (registerE dom w v ae) = false := rfl
  have core : translateCore rec (registerE dom w v ae) hint top named = pure none := rfl
  have control : isBoolControl (registerE dom w v ae) = false := rfl
  have mux : canonicalMuxType? (registerE dom w v ae) = none := rfl
  have setw : canonicalSetWidth? (registerE dom w v ae) = none := rfl
  have reg := canonicalRegister?_registerE (a := ae) hdom hw hv
  have step : translateStepWith translateFallback rec (registerE dom w v ae) hint top named =
      translateFallback rec (registerE dom w v ae) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, control, Bool.false_eq_true, if_false, mux, setw, reg]

/-! ## Non-interference helpers -/

/-- Assignments and registers only: the shape the certified register root
emits (memories and instances never appear on this path). -/
def SeqBody (body : List Stmt) : Prop :=
  ∀ st ∈ body, (∃ l r, st = .assign l r) ∨
    (∃ o c rk i iv, st = .register o c rk i iv)

theorem writesOf_tail {st : Stmt} {rest : List Stmt} {z : String}
    (h : z ∉ Sparkle.IR.Reorder.writesOf (st :: rest)) :
    z ∉ Sparkle.IR.Reorder.writesOf rest := by
  intro hm
  apply h
  simp only [Sparkle.IR.Reorder.writesOf, List.flatMap_cons, List.mem_append]
  exact Or.inr (by simpa [Sparkle.IR.Reorder.writesOf] using hm)

theorem writesOf_assign_head {l : String} {r : Sparkle.IR.AST.Expr} {rest : List Stmt} :
    l ∈ Sparkle.IR.Reorder.writesOf (.assign l r :: rest) := by
  simp [Sparkle.IR.Reorder.writesOf, Sparkle.IR.Reorder.stmtWrites]

theorem evalAssigns_preserved {we : WEnv} {mems : MEnv} :
    ∀ {body : List Stmt} {env result : Env} {z : String}, SeqBody body →
      evalAssigns we mems body env = some result →
      z ∉ Sparkle.IR.Reorder.writesOf body → result z = env z
  | [], env, result, z, _, h, _ => by cases h; rfl
  | st :: rest, env, result, z, hs, h, hz => by
    rcases hs st List.mem_cons_self with ⟨l, r, rfl⟩ | ⟨o, c, rk, i, iv, rfl⟩
    · simp only [evalAssigns, bind, Option.bind_eq_some_iff] at h
      obtain ⟨val, hv, he⟩ := h
      have hzl : z ≠ l := by
        intro eq; subst z
        exact hz writesOf_assign_head
      have step := evalAssigns_preserved (fun st hm => hs st (List.mem_cons_of_mem _ hm)) he
        (writesOf_tail hz)
      simpa [hzl] using step
    · simp only [evalAssigns] at h
      exact evalAssigns_preserved (fun st hm => hs st (List.mem_cons_of_mem _ hm)) h
        (writesOf_tail hz)

theorem evalAssigns_append {we : WEnv} {mems : MEnv} :
    ∀ {b1 b2 : List Stmt} {env : Env}, SeqBody b1 →
      evalAssigns we mems (b1 ++ b2) env =
        (evalAssigns we mems b1 env).bind (evalAssigns we mems b2)
  | [], _, env, _ => by simp [evalAssigns]
  | st :: rest, b2, env, hs => by
    rcases hs st List.mem_cons_self with ⟨l, r, rfl⟩ | ⟨o, c, rk, i, iv, rfl⟩
    · simp only [List.cons_append, evalAssigns]
      cases evalExpr we env r with
      | none => rfl
      | some val =>
        simpa using evalAssigns_append (fun st hm => hs st (List.mem_cons_of_mem _ hm))
    · simpa [evalAssigns] using
        evalAssigns_append (fun st hm => hs st (List.mem_cons_of_mem _ hm))

theorem regNexts_skip_assigns {we : WEnv} {mems : MEnv} {env : Env} :
    ∀ {b1 b2 : List Stmt}, (∀ st ∈ b1, ∃ l r, st = .assign l r) →
      regNexts we mems (b1 ++ b2) env = regNexts we mems b2 env
  | [], _, _ => rfl
  | st :: rest, b2, hs => by
    obtain ⟨l, r, rfl⟩ := hs st List.mem_cons_self
    simpa [regNexts] using
      regNexts_skip_assigns (fun st hm => hs st (List.mem_cons_of_mem _ hm))

theorem memNexts_seq {we : WEnv} {env : Env} :
    ∀ {body : List Stmt} {mems : MEnv}, SeqBody body →
      memNexts we body mems env = some mems
  | [], _, _ => rfl
  | st :: rest, mems, hs => by
    rcases hs st List.mem_cons_self with ⟨l, r, rfl⟩ | ⟨o, c, rk, i, iv, rfl⟩ <;>
      simpa [memNexts] using memNexts_seq (fun st hm => hs st (List.mem_cons_of_mem _ hm))

theorem not_allocated_rst : ¬ Sparkle.IR.NameHints.Allocated "rst" := by
  intro h
  have := h.2
  revert this
  decide

theorem not_allocated_out : ¬ Sparkle.IR.NameHints.Allocated "out" := by
  intro h
  have := h.2
  revert this
  decide

theorem dzStmt_assign (wm : Sparkle.IR.Optimize.WidthMap) (l : String)
    (r : Sparkle.IR.AST.Expr) {k : Nat} (hg : wm.get? l = some k) (hk : k ≠ 0) :
    Sparkle.IR.ZeroWidth.dzStmt wm (.assign l r) =
      some (.assign l (Sparkle.IR.ZeroWidth.dzExpr wm r)) := by
  simp only [Sparkle.IR.ZeroWidth.dzStmt, hg]
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rfl

theorem weOf_congr_wires {M N : Sparkle.IR.AST.Module} (h : M.wires = N.wires) :
    weOf M = weOf N := by
  funext x
  unfold Tools.ShippingEntrySoundness.weOf
  rw [h]

/-! ## Entry-state plumbing -/

theorem init_translateRecord (name : String) : (CircuitM.init name).translateRecord = {} := rfl
theorem init_body (name : String) : (CircuitM.init name).module.body = [] := rfl
theorem init_wires (name : String) : (CircuitM.init name).module.wires = [] := rfl
theorem init_outputs (name : String) : (CircuitM.init name).module.outputs = [] := rfl

/-- Zero values are admissible against the all-zero environment. -/
theorem admissible_zero : ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
    Admissible (fun _ => false) (fun _ _ => 0) (fun _ => 0) L a
  | [], _ => trivial
  | b :: rest, a => by
    refine ⟨?_, admissible_zero rest _⟩
    rcases b with ⟨⟨name, kind⟩, id⟩
    cases kind with
    | domain => trivial
    | bool => simp [InputValue, Tools.ShippingMuxLoweringSoundness.encodeBool]
    | bits n => simp [InputValue]

/-- Every prepared input-port wire carries an allocated (generated) name. -/
theorem prepare_wires_allocated (bools : FVarId → Bool)
    (bits : (id : FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a : Setup),
      (∀ q ∈ a.state.module.wires, Sparkle.IR.NameHints.Allocated q.name) →
      ∀ q ∈ (prepare bools bits L a).state.module.wires,
        Sparkle.IR.NameHints.Allocated q.name
  | [], _, ha => ha
  | b :: rest, a, ha => by
    rcases b with ⟨⟨name, kind⟩, id⟩
    cases kind with
    | domain => exact prepare_wires_allocated bools bits rest a ha
    | bool =>
      refine prepare_wires_allocated bools bits rest _ ?_
      intro q hq
      rw [show (extend a ((name, .bool), id) bools bits).state =
        Tools.ShippingMixedInputSoundness.inputState a.state name.toString .bit from rfl] at hq
      change q ∈ (CircuitM.makeWire name.toString .bit true a.state).2.module.wires at hq
      rw [(CircuitM.makeWire_spec name.toString .bit true a.state).2.2.2] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact CircuitM.makeWire_allocated name.toString .bit true a.state
      · exact ha q hq
    | bits n =>
      refine prepare_wires_allocated bools bits rest _ ?_
      intro q hq
      rw [show (extend a ((name, .bits n), id) bools bits).state =
        Tools.ShippingMixedInputSoundness.inputState a.state name.toString (.bitVector n) from rfl] at hq
      change q ∈ (CircuitM.makeWire name.toString (.bitVector n) true a.state).2.module.wires at hq
      rw [(CircuitM.makeWire_spec name.toString (.bitVector n) true a.state).2.2.2] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact CircuitM.makeWire_allocated name.toString (.bitVector n) true a.state
      · exact ha q hq

/-- The prepared context and builder state do not depend on the chosen
source values (only the valuation bookkeeping does). -/
theorem prepare_const (b1 b2 : FVarId → Bool)
    (v1 v2 : (id : FVarId) → (n : Nat) → BitVec n) :
    ∀ (L : List ((Name × MixedGateBinder) × FVarId)) (a1 a2 : Setup),
      a1.context = a2.context → a1.state = a2.state →
      (prepare b1 v1 L a1).context = (prepare b2 v2 L a2).context ∧
      (prepare b1 v1 L a1).state = (prepare b2 v2 L a2).state
  | [], a1, a2, hc, hs => ⟨hc, hs⟩
  | b :: rest, a1, a2, hc, hs => by
    rcases b with ⟨⟨name, kind⟩, id⟩
    cases kind with
    | domain => exact prepare_const b1 b2 v1 v2 rest a1 a2 hc hs
    | bool =>
      exact prepare_const b1 b2 v1 v2 rest _ _ (by simp [extend, hc, hs]) (by simp [extend, hs])
    | bits n =>
      exact prepare_const b1 b2 v1 v2 rest _ _ (by simp [extend, hc, hs]) (by simp [extend, hs])

/-! ## Cycle-level preservation from the actual mixed entry -/

/-- One `stepModule` cycle of the compiled register module: `out` observes the
current register value, and the register steps by the source recurrence, with
reset low. `r` is produced per instantiated source shape; both facts hold for
every admissible per-cycle seeding, so a caller can iterate them along any
input trace. -/
def RegisterPreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (binp vinp : Nat → FVarId)
      {w v : Nat} (e : Term (.bits w)),
    (dom.isFVar || dom.isBVar) = true → e.WF kb kv vw → v < 2 ^ w →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      registerE dom w v (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e) →
    ∃ r : String,
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (mems : MEnv)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (n : Nat) → BitVec n),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨vw j, vvals j (vw j)⟩) →
    env0 "rst" = 0 →
    weOf m r = w ∧
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
    weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
    ∃ envF, stepModule (weOf m) m.body env0 mems =
        some (envF, [(r, (eval bvals vvals e).toNat)], mems) ∧
      envF "out" = env0 r

set_option maxHeartbeats 1000000 in
theorem synthesizeMixedCertified_register_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    RegisterPreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, _⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw binp vinp w v e hdom he hv qeq
  -- Decompose the returned translation once; this is valuation-independent.
  have leaf := prepare_returns (bs.zip ids) (start (entryCompilerState false cache) declName.toString) (bools := fun _ => false)
    (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨rW, sm, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  -- Unfold one step of the fuel fixpoint at the root.
  have stepEq : translateExprToWire (registerE dom w v
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)) "out" false true =
      translateControlCachedWith (translateRegisterUncachedWith
          (translateFuelFix translateStep 1048575) w v)
        (registerE dom w v
          (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (registerE dom w v
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)) "out" false true = _
    rw [register_step _ dom _ w v hdom (e.wf_pos he) hv]
  rw [stepEq] at tr
  -- The prepared entry state has an empty record: the validated hit is dead.
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec rW rfl
    rw [record0] at dead
    simp at dead
  rw [registerUncached_registerE] at missRun
  obtain ⟨cw, sc, rc, remit⟩ := Returns.bind missRun
  obtain ⟨hrW, hsmR⟩ := emitRegister_returns remit
  have hrec := recordTranslation_returns record
  obtain ⟨hrE1, hrE2⟩ :=
    emitRegisterC_spec "out" "clk" "rst" (.ref cw) v (.bitVector w) true .asynchronous sc
  have mws := CircuitM.makeWire_spec "out" (.bitVector w) true sc
  have hrWm : rW = (CircuitM.makeWire "out" (.bitVector w) true sc).1 := hrW.trans hrE1
  -- Static shapes of the final translation state and the finished module.
  have smModule : sm.module = ((CircuitM.makeWire "out" (.bitVector w) true sc).2.module.addStmt
      (.register (CircuitM.makeWire "out" (.bitVector w) true sc).1 "clk"
        ("rst", .asynchronous) (.ref cw) v)) := by
    rw [hrec, hsmR, hrE2]
  have smUsed : sm.usedNames = (CircuitM.makeWire "out" (.bitVector w) true sc).2.usedNames := by
    rw [hrec, hsmR, hrE2]
  have stBody : st.module.body =
      .assign "out" (.ref rW) :: .register rW "clk" ("rst", .asynchronous) (.ref cw) v
        :: sc.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state]
    show _ :: (sm.module.addOutput _).body = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) p, (mo.addOutput p).body = mo.body from
      fun _ _ => rfl, smModule]
    show _ :: (_ :: (CircuitM.makeWire "out" (.bitVector w) true sc).2.module.body) = _
    rw [mws.2.2.1, ← hrWm]
  have stWires : st.module.wires = { name := rW, ty := .bitVector w } :: sc.module.wires := by
    rw [ht, emitAssign_wires, addOutput_state]
    show (sm.module.addOutput _).wires = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) p, (mo.addOutput p).wires = mo.wires from
      fun _ _ => rfl, smModule]
    show (CircuitM.makeWire "out" (.bitVector w) true sc).2.module.wires = _
    rw [mws.2.2.2, ← hrWm]
  have freshR : sc.usedNames.contains rW = false := by rw [hrWm]; exact mws.1
  have mBody : m.body = sc.module.body.reverse ++
      [.register rW "clk" ("rst", .asynchronous) (.ref cw) v, .assign "out" (.ref rW)] := by
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).body = _
    simp only [Module.finalize, (addClockReset_facts st.module).1, stBody]
    simp
  have mWires : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  refine ⟨rW, ?_⟩
  intro bools bits env0 mems bvals vvals a p adm hb0 hv0 hrst0
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids) (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [pc, ps] at rc
  have hb' : ∀ j, j < kb →
      inputValues (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits (binp j) =
        some (.bool (bvals j)) :=
    fun j hj => inputValues_bool (hb0 j hj)
  have separate := prepared.1.separate prepared.2.1
  have hv' : ∀ j, j < kv →
      inputValues (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits (vinp j) =
        some (.bits (vw j) (vvals j (vw j))) :=
    fun j hj => inputValues_bits separate (hv0 j hj)
  have contract := fuel_contract 1048575 (ctx := (prepare bools bits (bs.zip ids) (start (entryCompilerState false cache) declName.toString)).context) (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' e he
  have lookup := lookup_of_ports prepared.1 prepared.2.1
  have frame := contract.frame "reg_in" false false _ sc cw lookup rc
  have wiresSc : WiresOk sc := frame.wires prepared.2.1
  have rNotSc : rW ∉ sc.module.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    have := wiresSc.2 q hq
    rw [eq, freshR] at this
    cases this
  have stUsed : st.usedNames = ((sc.usedNames.insert rW).insert "out") := by
    rw [ht, emitAssign_usedNames, addOutput_state]
    show (sm.usedNames.insert "out") = _
    rw [smUsed, mws.2.1, ← hrWm]
  have wiresSt : WiresOk st := by
    constructor
    · rw [stWires]
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨rNotSc, wiresSc.1⟩
    · intro q hq
      rw [stWires] at hq
      rw [stUsed]
      rcases List.mem_cons.mp hq with rfl | hq
      · simp [Std.HashSet.contains_insert]
      · have := wiresSc.2 q hq
        simp [Std.HashSet.contains_insert, this]
  -- Every wire name is allocated; "rst" and "out" therefore have width 0.
  have allocSt : ∀ q ∈ st.module.wires, Sparkle.IR.NameHints.Allocated q.name := by
    intro q hq
    rw [stWires] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [hrWm]; exact CircuitM.makeWire_allocated "out" (.bitVector w) true sc
    · rcases frame.wireNames q hq with hold | halloc
      · exact prepare_wires_allocated bools bits (bs.zip ids) _
          (by rw [show (start (entryCompilerState false cache) declName.toString).state =
              CircuitM.init declName.toString from rfl, init_wires]; intro x hx; cases hx)
          q hold
      · exact halloc
  have widthRst : declaredWidths st "rst" = 0 := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    cases hf : st.module.wires.find? (fun p => p.name == "rst") with
    | none => simp [hf]
    | some q =>
      have hq := List.mem_of_find?_eq_some hf
      have eq : q.name = "rst" := by simpa using List.find?_some hf
      exact absurd (eq ▸ allocSt q hq) not_allocated_rst
  -- Run the child once at this cycle's seed.
  have widths : ScalarWidthsAgree (declaredWidths st) sc := by
    intro q hq
    exact declaredWidths_agree wiresSt q (by rw [stWires]; exact List.mem_cons_of_mem _ hq)
  have inv0 : Inv _ (inputValues _ _) (declaredWidths st) mems env0 _ env0 :=
    initial_unified
      (by rw [prepared.2.2.1]; rfl)
      (by rw [prepared.2.2.2]; rfl)
      separate
      (prepared.1.inputs prepared.2.1
        (by intro q hq; rw [stWires]
            exact List.mem_cons_of_mem _ (frame.decls q hq))
        (declaredWidths_agree wiresSt))
  have outcome := contract.sem "reg_in" false false _ sc cw env0 inv0 widths rc
  obtain ⟨res, invC, valCw, frameVals⟩ := outcome.execution
  have ordered := fuel_orders 1048575 (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' e he "reg_in" false _ sc cw env0 rc inv0 widths
    (OrderInv.empty (by rw [prepared.2.2.1]; rfl))
  -- The child cone is a pure assignment list; nothing writes r, rst or out.
  have seqSc : SeqBody sc.module.finalize.body := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := invC.typed stq (by
      change stq ∈ sc.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact Or.inl ⟨l, rhs, eq⟩
  have preAssigns : ∀ stq ∈ sc.module.finalize.body, ∃ l rhs, stq = .assign l rhs := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := invC.typed stq (by
      change stq ∈ sc.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact ⟨l, rhs, eq⟩
  have preEq : sc.module.finalize.body = sc.module.body.reverse := by
    simp [Module.finalize]
  have rNotW : rW ∉ Sparkle.IR.Reorder.writesOf sc.module.finalize.body := by
    intro hwr
    have hf := writes_mem_footprint hwr
    rw [preEq] at hf
    have hfp := (footprint_reverse_mem _ _).mp hf
    have := ordered.2 rW hfp
    rw [freshR] at this; cases this
  have rstNotW : "rst" ∉ Sparkle.IR.Reorder.writesOf sc.module.finalize.body := by
    intro hwr
    obtain ⟨stq, hst, hz⟩ := List.mem_flatMap.mp hwr
    obtain ⟨l, rhs, eq, htyped⟩ := invC.typed stq (by
      rw [preEq] at hst; exact List.mem_reverse.mp hst)
    subst eq
    simp only [Sparkle.IR.Reorder.stmtWrites, List.mem_singleton] at hz
    subst hz
    have pos := htyped.positive
    rw [widthRst] at pos
    exact Nat.lt_irrefl 0 pos
  have runsC : evalAssigns (declaredWidths st) mems sc.module.finalize.body env0 = some res :=
    invC.runs
  have resR : res rW = env0 rW := evalAssigns_preserved seqSc runsC rNotW
  have resRst : res "rst" = env0 "rst" := evalAssigns_preserved seqSc runsC rstNotW
  have cwUsed : sc.usedNames.contains cw = true := outcome.used
  have cwNotOut : cw ≠ "out" := by
    intro eq
    have hmem : sm.usedNames.contains cw = true := by
      rw [smUsed, mws.2.1]
      simp [Std.HashSet.contains_insert, cwUsed]
    rw [eq, freshOut] at hmem; cases hmem
  have rNotOut : rW ≠ "out" := by
    intro eq
    have hmem : sm.usedNames.contains rW = true := by
      rw [smUsed, mws.2.1, ← hrWm]
      simp [Std.HashSet.contains_insert]
    rw [eq, freshOut] at hmem; cases hmem
  have wR : declaredWidths st rW = w := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    rw [stWires]
    simp [List.find?, Sparkle.IR.Type.HWType.bitWidth]
  let envF : Env := fun n => if n = "out" then res rW else res n
  have evalFull : evalAssigns (declaredWidths st) mems m.body env0 = some envF := by
    rw [mBody, ← preEq, evalAssigns_append seqSc, runsC]
    show evalAssigns _ mems
      (.register rW "clk" ("rst", .asynchronous) (.ref cw) v ::
        .assign "out" (.ref rW) :: []) res = _
    simp [evalAssigns, evalExpr, envF]
  have hcwF : envF cw = (eval bvals vvals e).toNat := by
    simp only [envF, if_neg cwNotOut]
    exact valCw
  have hrstF : envF "rst" = 0 := by
    have : ("rst" : String) ≠ "out" := by decide
    simp only [envF, if_neg this]
    rw [resRst, hrst0]
  have nexts : regNexts (declaredWidths st) mems m.body envF =
      some [(rW, (eval bvals vvals e).toNat)] := by
    rw [mBody, ← preEq, regNexts_skip_assigns preAssigns]
    show regNexts _ mems
      (.register rW "clk" ("rst", .asynchronous) (.ref cw) v ::
        .assign "out" (.ref rW) :: []) envF = _
    have maskEq : mask (declaredWidths st rW) (eval bvals vvals e).toNat =
        (eval bvals vvals e).toNat := by
      rw [wR]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    simp [regNexts, evalExpr, hcwF, hrstF, maskEq]
  have seqM : SeqBody m.body := by
    rw [mBody, ← preEq]
    intro stq hq
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl (preAssigns stq hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inr ⟨_, _, _, _, _, rfl⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl ⟨_, _, rfl⟩
        · cases hq
  have mem0 : memNexts (declaredWidths st) m.body mems envF = some mems := memNexts_seq seqM
  have scalarSt : ScalarWires st := by
    intro q hq
    rw [stWires] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr ⟨w, rfl⟩
    · exact frame.scalar (prepare_shape (bs.zip ids) _ (by intro q hq'; rw [show
        (start (entryCompilerState false cache) declName.toString).state =
          CircuitM.init declName.toString from rfl, init_wires] at hq'; cases hq')).1 q hq
  have wm : weOf m = declaredWidths st := by
    rw [weOf_eq_moduleWidths (by
      intro q hq; rw [mWires, List.mem_reverse] at hq; exact scalarSt q hq)]
    exact moduleWidths_finish mWires wiresSt
  -- Sequential zero-width cleanup is the identity on this shape.
  have nodupM : (m.wires.map (·.name)).Nodup := by
    rw [mWires, List.map_reverse]
    exact nodup_reverse wiresSt.1
  have allocM : ∀ q ∈ m.wires, Sparkle.IR.NameHints.Allocated q.name := by
    intro q hq
    rw [mWires, List.mem_reverse] at hq
    exact allocSt q hq
  have outNotWire : "out" ∉ m.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    exact not_allocated_out (eq ▸ allocM q hq)
  have smWires2 : sm.module.wires = { name := rW, ty := .bitVector w } :: sc.module.wires := by
    rw [smModule]
    rw [show ∀ (mo : Sparkle.IR.AST.Module) s, (mo.addStmt s).wires = mo.wires from
      fun _ _ => rfl]
    rw [mws.2.2.2, ← hrWm]
  have tyEq : ty = .bitVector w := by
    rw [hty]
    unfold Tools.ShippingEntrySoundness.leafOutputType
    rw [smWires2]
    simp [List.find?]
  have mOutputs : m.outputs = [{ name := "out", ty := ty }] := by
    have outputsSm : sm.module.outputs = [] := by
      rw [smModule]
      rw [show ∀ (mo : Sparkle.IR.AST.Module) s, (mo.addStmt s).outputs = mo.outputs from
        fun _ _ => rfl]
      rw [makeWire_outputs, frame.outputs,
        (prepare_shape (bs.zip ids) _ (by
          intro q hq'
          rw [show (start (entryCompilerState false cache) declName.toString).state =
            CircuitM.init declName.toString from rfl, init_wires] at hq'
          cases hq')).2]
      rfl
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).outputs = _
    simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
    rw [ht, emitAssign_outputs, addOutput_state]
    simp [Module.addOutput, outputsSm]
  have wmOut : (Sparkle.IR.Optimize.buildWidthMap m).get? "out" = some w := by
    unfold Sparkle.IR.Optimize.buildWidthMap
    rw [Tools.ShippingPostSoundness.wmFold_notin m.wires _ "out" outNotWire, mOutputs]
    simp [Std.HashMap.get?_insert, tyEq, Sparkle.IR.Type.HWType.bitWidth]
  have hwPos : 0 < w := e.wf_pos he
  have bodyEq : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split
    · rfl
    · show m.body.filterMap (Sparkle.IR.ZeroWidth.dzStmt (Sparkle.IR.Optimize.buildWidthMap m))
        = m.body
      apply Tools.ShippingPostSoundness.filterMap_eq_self
      intro stq hst
      rw [mBody] at hst
      rcases List.mem_append.mp hst with hpre | hrest
      · obtain ⟨l, rhs, rfl, htyped⟩ := invC.typed stq (List.mem_reverse.mp hpre)
        have hpos : 0 < weOf m l := by rw [wm]; exact htyped.positive
        have hg := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpos
        have htym : TypedExpr (weOf m) rhs (weOf m l) := by rw [wm]; exact htyped
        have hwmr : ∀ x ∈ Sparkle.IR.Reorder.refsOf rhs,
            Sparkle.IR.ZeroWidth.exprWidth (Sparkle.IR.Optimize.buildWidthMap m) (.ref x) ≠ 0 := by
          intro x hx
          have hpx := htym.refs_positive x hx
          have hgx := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpx
          simp only [Sparkle.IR.ZeroWidth.exprWidth, Std.HashMap.getD_eq_getD_getElem?,
            ← Std.HashMap.get?_eq_getElem?, hgx, Option.getD_some]
          omega
        rw [dzStmt_assign _ _ _ hg (by omega),
          Tools.ShippingTypedPostSoundness.dzExpr_typed htym _ hwmr]
      · rcases List.mem_cons.mp hrest with rfl | hrest
        · simp [Sparkle.IR.ZeroWidth.dzStmt, Sparkle.IR.ZeroWidth.dzExpr]
        · rcases List.mem_cons.mp hrest with rfl | hnil
          · rw [dzStmt_assign _ _ _ wmOut (by omega)]
            simp [Sparkle.IR.ZeroWidth.dzExpr]
          · cases hnil
  have weEq : weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split
    · rfl
    · exact (weOf_congr_wires rfl).trans (Tools.ShippingPostSoundness.weOf_dropWires m nodupM)
  refine ⟨by rw [wm]; exact wR, bodyEq, weEq, envF, ?_, by simp [envF, resR]⟩
  rw [wm]
  unfold stepModule
  simp [evalFull, nexts, mem0, bind]

/-! ## The enabled register root -/

/-- `Signal.registerWithEnable (BitVec.ofNat w v) en a`, as the library call
elaborates over a polymorphic domain. -/
def registerEnableE (dom : Lean.Expr) (w v : Nat) (en a : Lean.Expr) : Lean.Expr :=
  mkApp5 (.const ``Sparkle.Core.Signal.Signal.registerWithEnable [.zero]) dom (bitVecE w)
    (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v)) en a

theorem canonicalRegisterEnable?_registerEnableE {dom en a : Lean.Expr} {w v : Nat}
    (hdom : (dom.isFVar || dom.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w) :
    canonicalRegisterEnable? (registerEnableE dom w v en a) = some (w, v, en, a) := by
  have hlit := litValue_natE w v hv
  simp only [mkApp2, mkAppB, mkApp] at hlit
  simp only [registerEnableE, mkApp5, mkApp4, mkApp2, mkAppB, mkApp, bitVecE,
    canonicalRegisterEnable?, hdom, if_true, canonicalNatLitValue?_natE, hlit]
  simp [hw]

theorem instFVars_registerEnableE (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr)
    (w v : Nat) (en a : Lean.Expr) :
    instFVars xs d (registerEnableE dom w v en a) =
      registerEnableE (instFVars xs d dom) w v (instFVars xs d en) (instFVars xs d a) := rfl

theorem unifiedRegisterRoot_registerEnableE {kinds : Array MixedGateBinder}
    {dom en a : Lean.Expr} {w v : Nat}
    (hdom : (dom.isFVar || dom.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (henB : unifiedGateBoolBody kinds en = true)
    (body : unifiedGateBitsBody kinds w a = true) :
    unifiedRegisterRoot kinds (registerEnableE dom w v en a) = true := by
  unfold unifiedRegisterRoot
  have hreg : canonicalRegister? (registerEnableE dom w v en a) = none := rfl
  rw [hreg, canonicalRegisterEnable?_registerEnableE hdom hw hv]
  simp [hw, henB, body]

theorem registerEnable_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {w v : Nat} {kb kv : Nat} {vw : Nat → Nat}
    {bpos vpos : Nat → Nat} {en : Term .bool} {e : Term (.bits w)}
    (peel : mixedGatePeel d.value = some (bs, registerEnableE dom w v
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) en)
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e)))
    (hdom : (dom.isFVar || dom.isBVar) = true) (hv : v < 2 ^ w)
    (hen : en.WF kb kv vw) (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∀ isInst, mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, registerEnableE dom w v
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) en)
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e)) := by
  intro isInst
  have henB : unifiedGateBoolBody (bs.map Prod.snd).toArray
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) en) = true :=
    unified_quote_accepted
      (fun j hj => (hb j hj).elim fun name pos => input_bool_accepted pos)
      (fun j hj => (hvp j hj).elim fun name pos => input_bits_accepted pos) en hen
  have body : unifiedGateBitsBody (bs.map Prod.snd).toArray w
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) = true :=
    unified_quote_accepted
      (fun j hj => (hb j hj).elim fun name pos => input_bool_accepted pos)
      (fun j hj => (hvp j hj).elim fun name pos => input_bits_accepted pos) e he
  have root := unifiedRegisterRoot_registerEnableE hdom (e.wf_pos he) hv henB body
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, Bool.or_true, Bool.true_or, if_true]

set_option maxHeartbeats 1000000 in
theorem registerEnableUncached_registerEnableE (rec : TranslateFn) (dom en ae : Lean.Expr)
    (w v : Nat) (hint : String) (top named : Bool) :
    translateRegisterEnableUncachedWith rec w v (registerEnableE dom w v en ae)
        hint top named =
      (do
        let enW ← rec en "reg_en" false false
        let inW ← rec ae "reg_input" false false
        let muxW ← CompilerM.makeWire (hint ++ "_mux") (.bitVector w)
        let r ← CompilerM.emitRegister hint "clk" "rst" (.ref muxW) v (.bitVector w)
          (named := named)
        CompilerM.emitAssign muxW (.op .mux [.ref enW, .ref inW, .ref r])
        return r) := rfl

set_option maxHeartbeats 1000000 in
theorem registerEnable_step (rec : TranslateFn) (dom en ae : Lean.Expr) (w v : Nat)
    (hdom : (dom.isFVar || dom.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (registerEnableE dom w v en ae) hint top named =
      translateControlCachedWith (translateRegisterEnableUncachedWith rec w v)
        (registerEnableE dom w v en ae) hint top named := by
  have shape : translateCoreShape (registerEnableE dom w v en ae) = false := rfl
  have core : translateCore rec (registerEnableE dom w v en ae) hint top named =
    pure none := rfl
  have control : isBoolControl (registerEnableE dom w v en ae) = false := rfl
  have mux : canonicalMuxType? (registerEnableE dom w v en ae) = none := rfl
  have setw : canonicalSetWidth? (registerEnableE dom w v en ae) = none := rfl
  have reg : canonicalRegister? (registerEnableE dom w v en ae) = none := rfl
  have regEn := canonicalRegisterEnable?_registerEnableE (en := en) (a := ae) hdom hw hv
  have step : translateStepWith translateFallback rec (registerEnableE dom w v en ae)
      hint top named =
      translateFallback rec (registerEnableE dom w v en ae) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, control, Bool.false_eq_true, if_false, mux, setw, reg, regEn]

/-- One `stepModule` cycle of the compiled enabled-register module: `out`
observes the current register value, and the register updates to the input
cone's value when the enable cone is true, else holds. The seed's register
value must fit the width (the hold path stores it back). -/
def RegisterEnablePreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (binp vinp : Nat → FVarId)
      {w v : Nat} (en : Term .bool) (e : Term (.bits w)),
    (dom.isFVar || dom.isBVar) = true → en.WF kb kv vw → e.WF kb kv vw → v < 2 ^ w →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      registerEnableE dom w v
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) en)
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e) →
    ∃ r : String,
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (mems : MEnv)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (n : Nat) → BitVec n),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨vw j, vvals j (vw j)⟩) →
    env0 "rst" = 0 → env0 r < 2 ^ w →
    weOf m r = w ∧
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
    weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
    ∃ envF, stepModule (weOf m) m.body env0 mems =
        some (envF, [(r, if eval bvals vvals en then (eval bvals vvals e).toNat
          else env0 r)], mems) ∧
      envF "out" = env0 r

set_option maxHeartbeats 1000000 in
theorem synthesizeMixedCertified_registerEnable_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    RegisterEnablePreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, _⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw binp vinp w v en e hdom hen he hv qeq
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) (bools := fun _ => false)
    (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨rW, sm, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have stepEq : translateExprToWire (registerEnableE dom w v
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) en)
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)) "out" false true =
      translateControlCachedWith (translateRegisterEnableUncachedWith
          (translateFuelFix translateStep 1048575) w v)
        (registerEnableE dom w v
          (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) en)
          (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e))
        "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (registerEnableE dom w v
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) en)
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)) "out" false true = _
    rw [registerEnable_step _ dom _ _ w v hdom (e.wf_pos he) hv]
  rw [stepEq] at tr
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec rW rfl
    rw [record0] at dead
    simp at dead
  rw [registerEnableUncached_registerEnableE] at missRun
  obtain ⟨enW, se, rcEn, missRun⟩ := Returns.bind missRun
  obtain ⟨inW, sc, rcIn, missRun⟩ := Returns.bind missRun
  obtain ⟨muxW, s3, rmk, missRun⟩ := Returns.bind missRun
  obtain ⟨hmuxW, hs3⟩ := makeWire_returns rmk
  obtain ⟨rW2, s4, remit, missRun⟩ := Returns.bind missRun
  obtain ⟨hrW2, hs4⟩ := emitRegister_returns remit
  obtain ⟨u5, s5, rassign, rpure⟩ := Returns.bind missRun
  have hs5 := emitAssign_returns rassign
  obtain ⟨hrWeq, hsmR⟩ := Returns.pure rpure
  subst hrWeq
  have hrec := recordTranslation_returns record
  have mws3 := CircuitM.makeWire_spec ("out" ++ "_mux") (.bitVector w) false sc
  obtain ⟨hrE1, hrE2⟩ :=
    emitRegisterC_spec "out" "clk" "rst" (.ref muxW) v (.bitVector w) true .asynchronous s3
  have mws := CircuitM.makeWire_spec "out" (.bitVector w) true s3
  have hrWm : rW = (CircuitM.makeWire "out" (.bitVector w) true s3).1 := hrW2.trans hrE1
  have s4Module : s4.module = ((CircuitM.makeWire "out" (.bitVector w) true s3).2.module.addStmt
      (.register (CircuitM.makeWire "out" (.bitVector w) true s3).1 "clk"
        ("rst", .asynchronous) (.ref muxW) v)) := by
    rw [hs4, hrE2]
  have smModule : sm.module = s5.module := by rw [hrec, hsmR]
  have stBody : st.module.body =
      .assign "out" (.ref rW) ::
        .assign muxW (.op .mux [.ref enW, .ref inW, .ref rW]) ::
        .register rW "clk" ("rst", .asynchronous) (.ref muxW) v :: sc.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state]
    show _ :: (sm.module.addOutput _).body = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).body = mo.body from
      fun _ _ => rfl, smModule, hs5, emitAssign_body_cons, s4Module]
    show _ :: _ :: (_ :: (CircuitM.makeWire "out" (.bitVector w) true s3).2.module.body) = _
    rw [mws.2.2.1, ← hrWm, hs3, mws3.2.2.1]
  have stWires : st.module.wires = { name := rW, ty := .bitVector w } ::
      { name := muxW, ty := .bitVector w } :: sc.module.wires := by
    rw [ht, emitAssign_wires, addOutput_state]
    show (sm.module.addOutput _).wires = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).wires = mo.wires from
      fun _ _ => rfl, smModule, hs5, emitAssign_wires, s4Module]
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addStmt q).wires = mo.wires from
      fun _ _ => rfl]
    rw [mws.2.2.2, ← hrWm, hs3, mws3.2.2.2, ← hmuxW]
  have freshMux : sc.usedNames.contains muxW = false := by rw [hmuxW]; exact mws3.1
  have s3Used : s3.usedNames = sc.usedNames.insert muxW := by
    rw [hs3, mws3.2.1, ← hmuxW]
  have freshR3 : s3.usedNames.contains rW = false := by rw [hrWm]; exact mws.1
  have rNotSc : sc.usedNames.contains rW = false := by
    rw [s3Used] at freshR3
    by_cases h : sc.usedNames.contains rW = true
    · rw [Std.HashSet.contains_insert] at freshR3
      simp [h] at freshR3
    · simpa using h
  have rNeMux : rW ≠ muxW := by
    intro eq
    rw [s3Used, eq] at freshR3
    simp [Std.HashSet.contains_insert] at freshR3
  have smUsed : sm.usedNames = (sc.usedNames.insert muxW).insert rW := by
    rw [hrec, hsmR]
    show s5.usedNames = _
    rw [hs5, emitAssign_usedNames, hs4, hrE2]
    show (CircuitM.makeWire "out" (.bitVector w) true s3).2.usedNames = _
    rw [mws.2.1, ← hrWm, s3Used]
  have stUsed : st.usedNames = (((sc.usedNames.insert muxW).insert rW).insert "out") := by
    rw [ht, emitAssign_usedNames, addOutput_state]
    show (sm.usedNames.insert "out") = _
    rw [smUsed]
  have mBody : m.body = sc.module.body.reverse ++
      [.register rW "clk" ("rst", .asynchronous) (.ref muxW) v,
       .assign muxW (.op .mux [.ref enW, .ref inW, .ref rW]),
       .assign "out" (.ref rW)] := by
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).body = _
    simp only [Module.finalize, (addClockReset_facts st.module).1, stBody]
    simp
  have mWires : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  refine ⟨rW, ?_⟩
  intro bools bits env0 mems bvals vvals a p adm hb0 hv0 hrst0 hstb
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [pc, ps] at rcEn
  rw [pc] at rcIn
  have hb' : ∀ j, j < kb →
      inputValues (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits (binp j) =
        some (.bool (bvals j)) :=
    fun j hj => inputValues_bool (hb0 j hj)
  have separate := prepared.1.separate prepared.2.1
  have hv' : ∀ j, j < kv →
      inputValues (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits (vinp j) =
        some (.bits (vw j) (vvals j (vw j))) :=
    fun j hj => inputValues_bits separate (hv0 j hj)
  have contractEn := fuel_contract 1048575
    (ctx := (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context)
    (we := declaredWidths st) (mems := mems) (initial := env0) (dom := dom) hb' hv' en hen
  have contractIn := fuel_contract 1048575
    (ctx := (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context)
    (we := declaredWidths st) (mems := mems) (initial := env0) (dom := dom) hb' hv' e he
  have lookup := lookup_of_ports prepared.1 prepared.2.1
  have fEn := contractEn.frame "reg_en" false false _ se enW lookup rcEn
  have fIn := contractIn.frame "reg_input" false false se sc inW (lookup.transfer fEn) rcIn
  have wiresSc : WiresOk sc := fIn.wires (fEn.wires prepared.2.1)
  have muxNotSc : muxW ∉ sc.module.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    have := wiresSc.2 q hq
    rw [eq, freshMux] at this
    cases this
  have rNotScW : rW ∉ sc.module.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    have := wiresSc.2 q hq
    rw [eq, rNotSc] at this
    cases this
  have wiresSt : WiresOk st := by
    constructor
    · rw [stWires]
      simp only [List.map_cons, List.nodup_cons, List.mem_cons]
      refine ⟨?_, muxNotSc, wiresSc.1⟩
      rintro (h | h)
      · exact rNeMux h
      · exact rNotScW h
    · intro q hq
      rw [stWires] at hq
      rw [stUsed]
      rcases List.mem_cons.mp hq with rfl | hq
      · simp [Std.HashSet.contains_insert]
      · rcases List.mem_cons.mp hq with rfl | hq
        · simp [Std.HashSet.contains_insert]
        · have := wiresSc.2 q hq
          simp [Std.HashSet.contains_insert, this]
  have allocSt : ∀ q ∈ st.module.wires, Sparkle.IR.NameHints.Allocated q.name := by
    intro q hq
    rw [stWires] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [hrWm]; exact CircuitM.makeWire_allocated "out" (.bitVector w) true s3
    · rcases List.mem_cons.mp hq with rfl | hq
      · rw [hmuxW]; exact CircuitM.makeWire_allocated ("out" ++ "_mux") (.bitVector w) false sc
      · rcases fIn.wireNames q hq with hold | halloc
        · rcases fEn.wireNames q hold with hold2 | halloc2
          · exact prepare_wires_allocated bools bits (bs.zip ids) _
              (by rw [show (start (entryCompilerState false cache) declName.toString).state =
                  CircuitM.init declName.toString from rfl, init_wires]
                  intro x hx; cases hx)
              q hold2
          · exact halloc2
        · exact halloc
  have widthRst : declaredWidths st "rst" = 0 := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    cases hf : st.module.wires.find? (fun q => q.name == "rst") with
    | none => simp [hf]
    | some q =>
      have hq := List.mem_of_find?_eq_some hf
      have eq : q.name = "rst" := by simpa using List.find?_some hf
      exact absurd (eq ▸ allocSt q hq) not_allocated_rst
  have wR : declaredWidths st rW = w := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    rw [stWires]
    simp [List.find?, Sparkle.IR.Type.HWType.bitWidth]
  have widthsSc : ScalarWidthsAgree (declaredWidths st) sc := by
    intro q hq
    exact declaredWidths_agree wiresSt q (by
      rw [stWires]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  have widthsSe : ScalarWidthsAgree (declaredWidths st) se := by
    intro q hq
    exact widthsSc q (fIn.decls q hq)
  have inv0 : Inv _ (inputValues _ _) (declaredWidths st) mems env0 _ env0 :=
    initial_unified
      (by rw [prepared.2.2.1]; rfl)
      (by rw [prepared.2.2.2]; rfl)
      separate
      (prepared.1.inputs prepared.2.1
        (by intro q hq; rw [stWires]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (fIn.decls q (fEn.decls q hq))))
        (declaredWidths_agree wiresSt))
  have enOut := contractEn.sem "reg_en" false false _ se enW env0 inv0 widthsSe rcEn
  obtain ⟨res1, inv1, val1, fvals1⟩ := enOut.execution
  have inOut := contractIn.sem "reg_input" false false se sc inW res1 inv1 widthsSc rcIn
  obtain ⟨res2, inv2, val2, fvals2⟩ := inOut.execution
  have orderedEn := fuel_orders 1048575 (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' en hen "reg_en" false _ se enW env0 rcEn inv0
    widthsSe (OrderInv.empty (by rw [prepared.2.2.1]; rfl))
  have orderedIn := fuel_orders 1048575 (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' e he "reg_input" false se sc inW res1 rcIn inv1
    widthsSc orderedEn
  have seqSc : SeqBody sc.module.finalize.body := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := inv2.typed stq (by
      change stq ∈ sc.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact Or.inl ⟨l, rhs, eq⟩
  have preAssigns : ∀ stq ∈ sc.module.finalize.body, ∃ l rhs, stq = .assign l rhs := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := inv2.typed stq (by
      change stq ∈ sc.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact ⟨l, rhs, eq⟩
  have preEq : sc.module.finalize.body = sc.module.body.reverse := by
    simp [Module.finalize]
  have notWrites : ∀ z, sc.usedNames.contains z = false →
      z ∉ Sparkle.IR.Reorder.writesOf sc.module.finalize.body := by
    intro z hz hwr
    have hf := writes_mem_footprint hwr
    rw [preEq] at hf
    have hfp := (footprint_reverse_mem _ _).mp hf
    have := orderedIn.2 z hfp
    rw [hz] at this
    cases this
  have rstNotW : "rst" ∉ Sparkle.IR.Reorder.writesOf sc.module.finalize.body := by
    intro hwr
    obtain ⟨stq, hst, hz⟩ := List.mem_flatMap.mp hwr
    obtain ⟨l, rhs, eq, htyped⟩ := inv2.typed stq (by
      rw [preEq] at hst; exact List.mem_reverse.mp hst)
    subst eq
    simp only [Sparkle.IR.Reorder.stmtWrites, List.mem_singleton] at hz
    subst hz
    have pos := htyped.positive
    rw [widthRst] at pos
    exact Nat.lt_irrefl 0 pos
  have runsC : evalAssigns (declaredWidths st) mems sc.module.finalize.body env0 = some res2 :=
    inv2.runs
  have resR : res2 rW = env0 rW :=
    evalAssigns_preserved seqSc runsC (notWrites rW rNotSc)
  have resRst : res2 "rst" = env0 "rst" := evalAssigns_preserved seqSc runsC rstNotW
  have enUsedSe : se.usedNames.contains enW = true := enOut.used
  have resEn : res2 enW = Tools.ShippingMuxLoweringSoundness.encodeBool (eval bvals vvals en) :=
    (fvals2 enW enUsedSe).trans val1
  have freshOutSm : sm.usedNames.contains "out" = false := freshOut
  have rNotOut : rW ≠ "out" := by
    intro eq
    have hmem : sm.usedNames.contains rW = true := by
      rw [smUsed]
      simp [Std.HashSet.contains_insert]
    rw [eq, freshOutSm] at hmem; cases hmem
  have muxNotOut : muxW ≠ "out" := by
    intro eq
    have hmem : sm.usedNames.contains muxW = true := by
      rw [smUsed]
      simp [Std.HashSet.contains_insert]
    rw [eq, freshOutSm] at hmem; cases hmem
  have inUsedSc : sc.usedNames.contains inW = true := inOut.used
  have inNeMux : inW ≠ muxW := by
    intro eq; rw [eq, freshMux] at inUsedSc; cases inUsedSc
  have inNeR : inW ≠ rW := by
    intro eq; rw [eq, rNotSc] at inUsedSc; cases inUsedSc
  have enUsedSc : sc.usedNames.contains enW = true := fIn.used enW enUsedSe
  have enNeMux : enW ≠ muxW := by
    intro eq; rw [eq, freshMux] at enUsedSc; cases enUsedSc
  have enNeR : enW ≠ rW := by
    intro eq; rw [eq, rNotSc] at enUsedSc; cases enUsedSc
  have resIn : res2 inW = (eval bvals vvals e).toNat := val2
  have hmuxVal : evalExpr (declaredWidths st) res2
      (.op .mux [.ref enW, .ref inW, .ref rW]) =
      some (if eval bvals vvals en then (eval bvals vvals e).toNat else env0 rW) := by
    cases hEn : eval bvals vvals en <;>
      simp [evalExpr, evalList, evalOp, resEn, resIn, resR, hEn,
        Tools.ShippingMuxLoweringSoundness.encodeBool]
  let env3 : Env := fun n => if n = muxW then
    (if eval bvals vvals en then (eval bvals vvals e).toNat else env0 rW) else res2 n
  let envF : Env := fun n => if n = "out" then env3 rW else env3 n
  have evalFull : evalAssigns (declaredWidths st) mems m.body env0 = some envF := by
    rw [mBody, ← preEq, evalAssigns_append seqSc, runsC]
    show evalAssigns _ mems
      (.register rW "clk" ("rst", .asynchronous) (.ref muxW) v ::
        .assign muxW (.op .mux [.ref enW, .ref inW, .ref rW]) ::
        .assign "out" (.ref rW) :: []) res2 = _
    simp only [evalAssigns, bind]
    rw [hmuxVal]
    rfl
  have env3R : env3 rW = env0 rW := by
    simp only [env3, if_neg rNeMux]
    exact resR
  have envFMux : envF muxW =
      (if eval bvals vvals en then (eval bvals vvals e).toNat else env0 rW) := by
    simp [envF, env3, muxNotOut]
  have envFRst : envF "rst" = 0 := by
    have h1 : ("rst" : String) ≠ "out" := by decide
    have h2 : ("rst" : String) ≠ muxW := by
      intro eq
      have := allocSt { name := muxW, ty := .bitVector w } (by
        rw [stWires]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      rw [← eq] at this
      exact not_allocated_rst this
    simp only [envF, env3, if_neg h1, if_neg h2]
    rw [resRst, hrst0]
  have nexts : regNexts (declaredWidths st) mems m.body envF =
      some [(rW, if eval bvals vvals en then (eval bvals vvals e).toNat else env0 rW)] := by
    rw [mBody, ← preEq, regNexts_skip_assigns preAssigns]
    show regNexts _ mems
      (.register rW "clk" ("rst", .asynchronous) (.ref muxW) v ::
        .assign muxW (.op .mux [.ref enW, .ref inW, .ref rW]) ::
        .assign "out" (.ref rW) :: []) envF = _
    have maskEq : mask (declaredWidths st rW)
        (if eval bvals vvals en then (eval bvals vvals e).toNat else env0 rW) =
        (if eval bvals vvals en then (eval bvals vvals e).toNat else env0 rW) := by
      rw [wR]
      cases eval bvals vvals en with
      | true =>
        show BitVec.toNat (eval bvals vvals e) % 2 ^ w = _
        exact Nat.mod_eq_of_lt (BitVec.isLt _)
      | false =>
        show env0 rW % 2 ^ w = _
        exact Nat.mod_eq_of_lt hstb
    simp [regNexts, evalExpr, envFMux, envFRst, maskEq]
  have seqM : SeqBody m.body := by
    rw [mBody, ← preEq]
    intro stq hq
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl (preAssigns stq hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inr ⟨_, _, _, _, _, rfl⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inl ⟨_, _, rfl⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl ⟨_, _, rfl⟩
          · cases hq
  have mem0 : memNexts (declaredWidths st) m.body mems envF = some mems := memNexts_seq seqM
  have scalarSt : ScalarWires st := by
    intro q hq
    rw [stWires] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr ⟨w, rfl⟩
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inr ⟨w, rfl⟩
      · exact fIn.scalar (fEn.scalar (prepare_shape (bs.zip ids) _ (by
          intro q hq'
          rw [show (start (entryCompilerState false cache) declName.toString).state =
            CircuitM.init declName.toString from rfl, init_wires] at hq'
          cases hq')).1) q hq
  have wm : weOf m = declaredWidths st := by
    rw [weOf_eq_moduleWidths (by
      intro q hq; rw [mWires, List.mem_reverse] at hq; exact scalarSt q hq)]
    exact moduleWidths_finish mWires wiresSt
  -- Sequential zero-width cleanup is the identity on this shape too.
  have nodupM : (m.wires.map (·.name)).Nodup := by
    rw [mWires, List.map_reverse]
    exact nodup_reverse wiresSt.1
  have allocM : ∀ q ∈ m.wires, Sparkle.IR.NameHints.Allocated q.name := by
    intro q hq
    rw [mWires, List.mem_reverse] at hq
    exact allocSt q hq
  have outNotWire : "out" ∉ m.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    exact not_allocated_out (eq ▸ allocM q hq)
  have tyEq : ty = .bitVector w := by
    rw [hty]
    unfold Tools.ShippingEntrySoundness.leafOutputType
    rw [show sm.module.wires = { name := rW, ty := .bitVector w } ::
        { name := muxW, ty := .bitVector w } :: sc.module.wires from by
      rw [smModule, hs5, emitAssign_wires, s4Module]
      rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addStmt q).wires = mo.wires from
        fun _ _ => rfl]
      rw [mws.2.2.2, ← hrWm, hs3, mws3.2.2.2, ← hmuxW]]
    simp [List.find?]
  have mOutputs : m.outputs = [{ name := "out", ty := ty }] := by
    have outputsSm : sm.module.outputs = [] := by
      rw [smModule, hs5]
      show (CircuitM.emitAssign muxW _ s4).2.module.outputs = _
      rw [emitAssign_outputs, s4Module]
      rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addStmt q).outputs = mo.outputs from
        fun _ _ => rfl]
      rw [makeWire_outputs, hs3]
      rw [makeWire_outputs, fIn.outputs, fEn.outputs,
        (prepare_shape (bs.zip ids) _ (by
          intro q hq'
          rw [show (start (entryCompilerState false cache) declName.toString).state =
            CircuitM.init declName.toString from rfl, init_wires] at hq'
          cases hq')).2]
      rfl
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).outputs = _
    simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
    rw [ht, emitAssign_outputs, addOutput_state]
    simp [Module.addOutput, outputsSm]
  have wmOut : (Sparkle.IR.Optimize.buildWidthMap m).get? "out" = some w := by
    unfold Sparkle.IR.Optimize.buildWidthMap
    rw [Tools.ShippingPostSoundness.wmFold_notin m.wires _ "out" outNotWire, mOutputs]
    simp [Std.HashMap.get?_insert, tyEq, Sparkle.IR.Type.HWType.bitWidth]
  have hwPos : 0 < w := e.wf_pos he
  have wMux : declaredWidths st muxW = w := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    rw [stWires]
    have hne : ¬ (rW == muxW) = true := by simpa using rNeMux
    simp [List.find?, hne, Sparkle.IR.Type.HWType.bitWidth]
  have bodyEq : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split
    · rfl
    · show m.body.filterMap (Sparkle.IR.ZeroWidth.dzStmt (Sparkle.IR.Optimize.buildWidthMap m))
        = m.body
      apply Tools.ShippingPostSoundness.filterMap_eq_self
      intro stq hst
      rw [mBody] at hst
      rcases List.mem_append.mp hst with hpre | hrest
      · obtain ⟨l, rhs, rfl, htyped⟩ := inv2.typed stq (List.mem_reverse.mp hpre)
        have hpos : 0 < weOf m l := by rw [wm]; exact htyped.positive
        have hg := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpos
        have htym : TypedExpr (weOf m) rhs (weOf m l) := by rw [wm]; exact htyped
        have hwmr : ∀ x ∈ Sparkle.IR.Reorder.refsOf rhs,
            Sparkle.IR.ZeroWidth.exprWidth (Sparkle.IR.Optimize.buildWidthMap m) (.ref x) ≠ 0 := by
          intro x hx
          have hpx := htym.refs_positive x hx
          have hgx := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpx
          simp only [Sparkle.IR.ZeroWidth.exprWidth, Std.HashMap.getD_eq_getD_getElem?,
            ← Std.HashMap.get?_eq_getElem?, hgx, Option.getD_some]
          omega
        rw [dzStmt_assign _ _ _ hg (by omega),
          Tools.ShippingTypedPostSoundness.dzExpr_typed htym _ hwmr]
      · rcases List.mem_cons.mp hrest with rfl | hrest
        · simp [Sparkle.IR.ZeroWidth.dzStmt, Sparkle.IR.ZeroWidth.dzExpr]
        · rcases List.mem_cons.mp hrest with rfl | hrest
          · have hgMux : (Sparkle.IR.Optimize.buildWidthMap m).get? muxW = some w := by
              have hposM : 0 < weOf m muxW := by rw [wm, wMux]; omega
              have := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hposM
              rw [wm, wMux] at this
              exact this
            rw [dzStmt_assign _ _ _ hgMux (by omega)]
            simp [Sparkle.IR.ZeroWidth.dzExpr, Sparkle.IR.ZeroWidth.dzList]
          · rcases List.mem_cons.mp hrest with rfl | hnil
            · rw [dzStmt_assign _ _ _ wmOut (by omega)]
              simp [Sparkle.IR.ZeroWidth.dzExpr]
            · cases hnil
  have weEq : weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split
    · rfl
    · exact (weOf_congr_wires rfl).trans (Tools.ShippingPostSoundness.weOf_dropWires m nodupM)
  refine ⟨by rw [wm]; exact wR, bodyEq, weEq, envF, ?_, by simp [envF, env3R]⟩
  rw [wm]
  unfold stepModule
  simp [evalFull, nexts, mem0, bind]

/-! ## The feedback (loop) register root -/

/-- `Signal.loop (fun s => Signal.register (BitVec.ofNat w v) cone)`: the
outer domain is `domO`, the occurrences under the binder are `domI`
(one binder deeper), and the cone reads the register back as `.bvar 0`. -/
def loopRegisterE (domO domI inst : Lean.Expr) (w v : Nat) (cone : Lean.Expr) : Lean.Expr :=
  mkApp4 (.const ``Sparkle.Core.Signal.Signal.loop []) domO (bitVecE w) inst
    (.lam `s (sigT domO w)
      (mkApp4 (.const ``Sparkle.Core.Signal.Signal.register [.zero]) domI (bitVecE w)
        (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v)) cone) .default)

theorem canonicalLoopRegister?_loopRegisterE {domO domI inst cone : Lean.Expr} {w v : Nat}
    (hdom : (domO.isFVar || domO.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w) :
    canonicalLoopRegister? (loopRegisterE domO domI inst w v cone) = some (w, v, cone) := by
  have hlit := litValue_natE w v hv
  simp only [mkApp2, mkAppB, mkApp] at hlit
  simp only [loopRegisterE, mkApp4, mkApp2, mkAppB, mkApp, bitVecE,
    canonicalLoopRegister?, hdom, if_true, canonicalNatLitValue?_natE, hlit]
  simp [hw]

theorem instFVars_loopRegisterE (xs : Array Lean.Expr) (d : Nat)
    (domO domI inst : Lean.Expr) (w v : Nat) (cone : Lean.Expr) :
    instFVars xs d (loopRegisterE domO domI inst w v cone) =
      loopRegisterE (instFVars xs d domO) (instFVars xs (d + 1) domI)
        (instFVars xs d inst) w v (instFVars xs (d + 1) cone) := rfl

theorem lookupVar_returns {id : FVarId} {ctx : CompilerState} {s s' : CircuitState}
    {a : Option String} (h : Returns (CompilerM.lookupVar id) ctx s a s') :
    s' = s ∧ a = Tools.ShippingBindingsSoundness.visible ctx s.sourceBindings id := by
  obtain ⟨mctx, mref, cctx, cref, wo, wo', hrun⟩ := h
  change EST.Out.ok (CircuitM.lookupSourceBinding (ctx.varMap.lookup id) id.name s) wo =
    EST.Out.ok (a, s') wo' at hrun
  cases hrun
  refine ⟨rfl, ?_⟩
  cases hv : ctx.varMap.lookup id <;>
    simp [Tools.ShippingBindingsSoundness.visible, CircuitM.lookupSourceBinding, hv, Option.orElse]

theorem bindSourceVariable_returns {id : FVarId} {wire : String} {ctx : CompilerState}
    {s s' : CircuitState} {u : Unit}
    (h : Returns (CompilerM.bindSourceVariable id wire) ctx s u s') :
    s' = { s with sourceBindings := s.sourceBindings.insert id.name wire } := by
  obtain ⟨mctx, mref, cctx, cref, wo, wo', hrun⟩ := h
  change EST.Out.ok (CircuitM.bindSourceVariable id.name wire s) wo =
    EST.Out.ok (u, s') wo' at hrun
  cases hrun
  rfl

theorem emitRegisterStmt_returns {out clk rst : String} {input : Sparkle.IR.AST.Expr}
    {initVal : Nat} {ctx : CompilerState} {s s' : CircuitState} {u : Unit}
    (h : Returns (CompilerM.emitRegisterStmt out clk rst input initVal) ctx s u s') :
    s' = { s with
      module := s.module.addStmt (.register out clk (rst, .asynchronous) input initVal) } := by
  unfold CompilerM.emitRegisterStmt at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  subst hcs hs1
  exact Returns.set k1

set_option maxHeartbeats 1000000 in
theorem loopRegisterUncached_loopRegisterE (rec : TranslateFn)
    (domO domI inst cone : Lean.Expr) (w v : Nat) (hint : String) (top named : Bool) :
    translateLoopRegisterUncachedWith rec w v (loopRegisterE domO domI inst w v cone)
        hint top named =
      (do
        let selfId ← CompilerM.liftMetaM Lean.mkFreshFVarId
        if (← CompilerM.lookupVar selfId).isSome then
          throw (Exception.error .missing "loop binder id collision")
        let r ← CompilerM.makeWire hint (.bitVector w) (named := named)
        CompilerM.bindSourceVariable selfId r
        let cw ← rec (instFVars #[.fvar selfId] 0 cone) "loop_body" false false
        CompilerM.emitRegisterStmt r "clk" "rst" (.ref cw) v
        return r) := rfl

set_option maxHeartbeats 1000000 in
theorem loopRegister_step (rec : TranslateFn) (domO domI inst cone : Lean.Expr) (w v : Nat)
    (hdom : (domO.isFVar || domO.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (loopRegisterE domO domI inst w v cone)
        hint top named =
      translateControlCachedWith (translateLoopRegisterUncachedWith rec w v)
        (loopRegisterE domO domI inst w v cone) hint top named := by
  have shape : translateCoreShape (loopRegisterE domO domI inst w v cone) = false := rfl
  have core : translateCore rec (loopRegisterE domO domI inst w v cone) hint top named =
    pure none := rfl
  have control : isBoolControl (loopRegisterE domO domI inst w v cone) = false := rfl
  have mux : canonicalMuxType? (loopRegisterE domO domI inst w v cone) = none := rfl
  have setw : canonicalSetWidth? (loopRegisterE domO domI inst w v cone) = none := rfl
  have reg : canonicalRegister? (loopRegisterE domO domI inst w v cone) = none := rfl
  have regEn : canonicalRegisterEnable? (loopRegisterE domO domI inst w v cone) = none := rfl
  have loopReg := canonicalLoopRegister?_loopRegisterE (domI := domI) (inst := inst)
    (cone := cone) hdom hw hv
  have step : translateStepWith translateFallback rec (loopRegisterE domO domI inst w v cone)
      hint top named =
      translateFallback rec (loopRegisterE domO domI inst w v cone) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, control, Bool.false_eq_true, if_false, mux, setw, reg,
    regEn, loopReg]

theorem fvarId_name_inj {a b : FVarId} (h : a.name = b.name) : a = b := by
  cases a; cases b; cases h; rfl

/-- One `stepModule` cycle of the compiled feedback-register module: the cone
may read the register back (as one more width-`w` source input, at term input
index `kv`), `out` observes the current value, and the register steps by the
cone's value at the current state. -/
def LoopRegisterPreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (dom domI inst : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (binp vinp : Nat → FVarId)
      {w v : Nat} (e : Term (.bits w)),
    (dom.isFVar || dom.isBVar) = true → vw kv = w → e.WF kb (kv + 1) vw → v < 2 ^ w →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      loopRegisterE dom domI inst w v
        (quote domI (fun j => .fvar (binp j))
          (fun j => if j = kv then .bvar 0 else .fvar (vinp j)) e) →
    ∃ r : String,
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (mems : MEnv)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (n : Nat) → BitVec n),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨vw j, vvals j (vw j)⟩) →
    env0 "rst" = 0 → env0 r < 2 ^ w →
    weOf m r = w ∧
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
    weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
    ∃ envF, stepModule (weOf m) m.body env0 mems =
        some (envF, [(r, (eval bvals
          (fun j n => if j = kv then BitVec.ofNat n (env0 r) else vvals j n) e).toNat)],
          mems) ∧
      envF "out" = env0 r

set_option maxHeartbeats 1000000 in
theorem synthesizeMixedCertified_loopRegister_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    LoopRegisterPreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, _⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom domI inst kb kv vw binp vinp w v e hdom hself he hv qeq
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) (bools := fun _ => false)
    (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨rW, sm, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have hw : 0 < w := by
    have := e.wf_pos he
    exact this
  have stepEq : translateExprToWire (loopRegisterE dom domI inst w v
        (quote domI (fun j => .fvar (binp j))
          (fun j => if j = kv then .bvar 0 else .fvar (vinp j)) e)) "out" false true =
      translateControlCachedWith (translateLoopRegisterUncachedWith
          (translateFuelFix translateStep 1048575) w v)
        (loopRegisterE dom domI inst w v
          (quote domI (fun j => .fvar (binp j))
            (fun j => if j = kv then .bvar 0 else .fvar (vinp j)) e)) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (loopRegisterE dom domI inst w v
        (quote domI (fun j => .fvar (binp j))
          (fun j => if j = kv then .bvar 0 else .fvar (vinp j)) e)) "out" false true = _
    rw [loopRegister_step _ dom domI inst _ w v hdom hw hv]
  rw [stepEq] at tr
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec rW rfl
    rw [record0] at dead
    simp at dead
  rw [loopRegisterUncached_loopRegisterE] at missRun
  obtain ⟨selfId, sf, rfresh, missRun⟩ := Returns.bind missRun
  have hsf : sf = _ := Returns.liftMetaM rfresh
  subst hsf
  obtain ⟨aOpt, sg, rlook, missRun⟩ := Returns.bind missRun
  obtain ⟨hsg, hvisEq⟩ := lookupVar_returns rlook
  subst hsg
  cases hopt : aOpt.isSome with
  | true =>
    rw [hopt] at missRun
    simp only [if_true] at missRun
    obtain ⟨_, _, hthrow, _⟩ := Returns.bind missRun
    exact (Returns.throw hthrow).elim
  | false =>
    rw [hopt] at missRun
    simp only [Bool.false_eq_true, if_false] at missRun
    have hvis : Tools.ShippingBindingsSoundness.visible
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings
        selfId = none := by
      rw [← hvisEq]
      exact Option.not_isSome_iff_eq_none.mp (by simp [hopt])
    have missRun2 : Returns (do
        let r ← CompilerM.makeWire "out" (.bitVector w) (named := true)
        CompilerM.bindSourceVariable selfId r
        let cw ← translateFuelFix translateStep 1048575
          (instFVars #[.fvar selfId] 0
            (quote domI (fun j => .fvar (binp j))
              (fun j => if j = kv then .bvar 0 else .fvar (vinp j)) e))
          "loop_body" false false
        CompilerM.emitRegisterStmt r "clk" "rst" (.ref cw) v
        pure r)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state rW smR := missRun
    obtain ⟨r0, s1, rmk, missRun3⟩ := Returns.bind missRun2
    obtain ⟨hr0, hs1⟩ := makeWire_returns rmk
    obtain ⟨ub, s2, rbind, missRun4⟩ := Returns.bind missRun3
    have hs2 := bindSourceVariable_returns rbind
    obtain ⟨cw, sc, rc, missRun5⟩ := Returns.bind missRun4
    obtain ⟨ue, s4, remit, rpure⟩ := Returns.bind missRun5
    have hs4 := emitRegisterStmt_returns remit
    obtain ⟨hrWeq, hsmR⟩ := Returns.pure rpure
    subst hrWeq
    have hrec := recordTranslation_returns record
    -- Static shapes.
    have stBody : st.module.body =
        .assign "out" (.ref rW) ::
          .register rW "clk" ("rst", .asynchronous) (.ref cw) v :: sc.module.body := by
      rw [ht, emitAssign_body_cons, addOutput_state]
      show _ :: (sm.module.addOutput _).body = _
      rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).body = mo.body from
        fun _ _ => rfl, hrec]
      show _ :: smR.module.body = _
      rw [hsmR, hs4]
      rfl
    have stWires : st.module.wires = sc.module.wires := by
      rw [ht, emitAssign_wires, addOutput_state]
      show (sm.module.addOutput _).wires = _
      rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).wires = mo.wires from
        fun _ _ => rfl, hrec]
      show smR.module.wires = _
      rw [hsmR, hs4]
      rfl
    have stUsed : st.usedNames = sc.usedNames.insert "out" := by
      rw [ht, emitAssign_usedNames, addOutput_state]
      show sm.usedNames.insert "out" = _
      rw [hrec]
      show smR.usedNames.insert "out" = _
      rw [hsmR, hs4]
    have mBody : m.body = sc.module.body.reverse ++
        [.register rW "clk" ("rst", .asynchronous) (.ref cw) v, .assign "out" (.ref rW)] := by
      rw [hm]
      show ((addClockResetIfSequential st.module).finalize).body = _
      simp only [Module.finalize, (addClockReset_facts st.module).1, stBody]
      simp
    have mWires : m.wires = st.module.wires.reverse := by
      rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
    refine ⟨rW, ?_⟩
    intro bools bits env0 mems bvals vvals a p adm hb0 hv0 hrst0 hstb
    have empty := empty_layout (entryCompilerState false cache) declName.toString env0
    have prepared := prepare_layout (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
    obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
      (bs.zip ids) _ _ rfl rfl
    rw [pc] at rc
    rw [ps] at hs1 hr0
    rw [pc, ps] at hvis
    have mws := CircuitM.makeWire_spec "out" (.bitVector w) true
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state
    have freshR : (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.usedNames.contains rW
        = false := by rw [hr0]; exact mws.1
    -- The fresh binder differs from every prepared input binder.
    have hvisVar : (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup selfId
        = none := by
      revert hvis
      unfold Tools.ShippingBindingsSoundness.visible
      cases (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup selfId
      · intro _; rfl
      · intro hcon; cases hcon
    have hvisPer : (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.get?
        selfId.name = none := by
      revert hvis
      unfold Tools.ShippingBindingsSoundness.visible
      rw [hvisVar]
      intro h; exact h
    have selfNe : ∀ id, Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings id ≠
        none → id ≠ selfId := by
      intro id hne heq
      subst heq
      exact hne hvis
    -- Bindings and visibility at the child entry state.
    have s2Bind : s2.sourceBindings = (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.insert
        selfId.name rW := by
      rw [hs2]
      show s1.sourceBindings.insert selfId.name rW = _
      rw [hs1, CircuitM.makeWire_sourceBindings]
    have s2Used : s2.usedNames = (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.usedNames.insert rW := by
      rw [hs2]
      show s1.usedNames = _
      rw [hs1, mws.2.1, hr0]
    have s2Module : s2.module = (CircuitM.makeWire "out" (.bitVector w) true
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state).2.module := by
      rw [hs2]
      show s1.module = _
      rw [hs1]
    have visSelf : Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        s2.sourceBindings selfId = some rW := by
      unfold Tools.ShippingBindingsSoundness.visible
      rw [hvisVar, s2Bind]
      simp [Std.HashMap.get?_insert]
    have visOld : ∀ id z, id ≠ selfId →
        Tools.ShippingBindingsSoundness.visible
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).context
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).state.sourceBindings id
          = some z →
        Tools.ShippingBindingsSoundness.visible
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).context
          s2.sourceBindings id = some z := by
      intro id z hne hz
      unfold Tools.ShippingBindingsSoundness.visible at hz ⊢
      rw [s2Bind]
      cases hvm : (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup id with
      | some u => rw [hvm] at hz; exact hz
      | none =>
        rw [hvm] at hz
        have hz' : (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.get?
            id.name = some z := hz
        have hname : ¬ (id.name == selfId.name) = true := by
          simp only [beq_iff_eq]
          intro h
          exact hne (fvarId_name_inj h)
        show ((prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.insert
            selfId.name rW).get? id.name = some z
        have hname' : ¬ (selfId.name = id.name) := fun h => hne (fvarId_name_inj h.symm)
        simpa [Std.HashMap.getElem?_insert, hname'] using hz'
    -- Extended per-cycle valuation: the loop binder is input `kv` at wire rW.
    have selfNeB : ∀ j, j < kb → binp j ≠ selfId := by
      intro j hj
      obtain ⟨wj, hbnd, -⟩ := prepared.1.bool (binp j) (bvals j) (hb0 j hj)
      exact selfNe _ (by rw [hbnd]; simp)
    have selfNeV : ∀ j, j < kv → vinp j ≠ selfId := by
      intro j hj
      obtain ⟨wj, hbnd, -⟩ := prepared.1.bits (vinp j) (vw j) (vvals j (vw j)) (hv0 j hj)
      exact selfNe _ (by rw [hbnd]; simp)
    have hb' : ∀ j, j < kb →
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id) (binp j) =
        some (.bool (bvals j)) := by
      intro j hj
      simp only [if_neg (selfNeB j hj)]
      exact inputValues_bool (hb0 j hj)
    have separate := prepared.1.separate prepared.2.1
    have hv' : ∀ j, j < kv + 1 →
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id)
          ((fun j => if j = kv then selfId else vinp j) j) =
        some (.bits (vw j)
          ((fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) j (vw j))) := by
      intro j hj
      by_cases hkv : j = kv
      · subst hkv
        have h1 : vw j = w := hself
        simp only [if_pos rfl]
        rw [← h1]
        simp
      · have hjlt : j < kv := by omega
        simp only [if_neg hkv, if_neg (selfNeV j hjlt)]
        exact inputValues_bits separate (hv0 j hjlt)
    have contract := fuel_contract 1048575
      (ctx := (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context)
      (inputs := fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
        else inputValues (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bits id)
      (we := declaredWidths st) (mems := mems) (initial := env0)
      (dom := instFVars #[.fvar selfId] 0 domI)
      (bi := binp) (vi := fun j => if j = kv then selfId else vinp j)
      (bools := bvals)
      (bits := fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n)
      hb' hv' e he
    have childEq : instFVars #[Lean.Expr.fvar selfId] 0
        (quote domI (fun j => .fvar (binp j))
          (fun j => if j = kv then .bvar 0 else .fvar (vinp j)) e) =
        quote (instFVars #[Lean.Expr.fvar selfId] 0 domI)
          (fun j => .fvar (binp j))
          (fun j => .fvar ((fun j => if j = kv then selfId else vinp j) j)) e := by
      rw [instFVars_quote]
      apply quote_congr _ _ e he
      · intro j hj
        rfl
      · intro j hj
        by_cases hkv : j = kv
        · subst hkv
          simp only [if_pos rfl]
          rfl
        · simp only [if_neg hkv]
          rfl
    rw [childEq] at rc
    have lookup2 : Lookup (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id) s2 := by
      constructor
      intro id val hval
      by_cases hid : id = selfId
      · subst hid
        refine ⟨rW, visSelf, ?_⟩
        rw [s2Used]
        simp [Std.HashSet.contains_insert]
      · rw [if_neg hid] at hval
        obtain ⟨wj, hbnd, hused⟩ :=
          (lookup_of_ports prepared.1 prepared.2.1).lookup id val hval
        refine ⟨wj, visOld id wj hid hbnd, ?_⟩
        rw [s2Used]
        simp [Std.HashSet.contains_insert, hused]
    have frame := contract.frame "loop_body" false false s2 sc cw lookup2 rc
    have wiresS2 : WiresOk s2 := by
      constructor
      · rw [s2Module, mws.2.2.2, ← hr0]
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, prepared.2.1.1⟩
        intro hmem
        obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
        have := prepared.2.1.2 q hq
        rw [eq, freshR] at this
        cases this
      · intro q hq
        rw [s2Module, mws.2.2.2, ← hr0] at hq
        rw [s2Used]
        rcases List.mem_cons.mp hq with rfl | hq
        · simp [Std.HashSet.contains_insert]
        · have := prepared.2.1.2 q hq
          simp [Std.HashSet.contains_insert, this]
    have wiresSc : WiresOk sc := frame.wires wiresS2
    have wiresSt : WiresOk st := by
      constructor
      · rw [stWires]; exact wiresSc.1
      · intro q hq
        rw [stWires] at hq
        rw [stUsed]
        have := wiresSc.2 q hq
        simp [Std.HashSet.contains_insert, this]
    have rMem : ({ name := rW, ty := .bitVector w } : Sparkle.IR.AST.Port) ∈
        st.module.wires := by
      rw [stWires]
      apply frame.decls
      rw [s2Module, mws.2.2.2, ← hr0]
      exact List.mem_cons_self
    have wR : declaredWidths st rW = w := declaredWidths_agree wiresSt _ rMem
    have widths : ScalarWidthsAgree (declaredWidths st) sc := by
      intro q hq
      exact declaredWidths_agree wiresSt q (by rw [stWires]; exact hq)
    have s2Body : s2.module.body = [] := by
      rw [s2Module, mws.2.2.1, prepared.2.2.1]
      rfl
    have runs2 : Runs (declaredWidths st) mems env0 s2 env0 := by
      unfold Runs
      have hfin : s2.module.finalize.body = [] := by simp [Module.finalize, s2Body]
      rw [hfin]
      rfl
    have growth : ∀ q ∈ (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.module.wires,
        q ∈ st.module.wires := by
      intro q hq
      rw [stWires]
      exact frame.decls q (by
        rw [s2Module, mws.2.2.2, ← hr0]
        exact List.mem_cons_of_mem _ hq)
    have mixedI := prepared.1.inputs prepared.2.1 growth (declaredWidths_agree wiresSt)
    have inputsInv : Tools.ShippingUnifiedInvariant.Inputs
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id)
        (declaredWidths st) s2 env0 := by
      constructor
      intro id val hval
      by_cases hid : id = selfId
      · subst hid
        simp only [if_pos rfl] at hval
        cases hval
        refine ⟨rW, visSelf, ?_, ?_, ?_⟩
        · rw [s2Used]
          simp [Std.HashSet.contains_insert]
        · show env0 rW = (Value.bits w (BitVec.ofNat w (env0 rW))).toNat
          simp [Value.toNat, Nat.mod_eq_of_lt hstb]
        · simpa using wR
      · simp only [if_neg hid] at hval
        obtain ⟨wj, hbnd, hused, hval2, hwid⟩ :=
          (Tools.ShippingUnifiedInvariant.Inputs.of_mixed mixedI).lookup id val hval
        refine ⟨wj, visOld id wj hid hbnd, ?_, hval2, hwid⟩
        rw [s2Used]
        simp [Std.HashSet.contains_insert, hused]
    have s2Record : s2.translateRecord = {} := by
      rw [hs2]
      show s1.translateRecord = {}
      rw [hs1, CircuitM.makeWire_translateRecord, prepared.2.2.2]
      rfl
    have inv2 : Inv (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id)
        (declaredWidths st) mems env0 s2 env0 :=
      ⟨runs2, inputsInv, Records.empty s2Record, by
        intro stq hq
        rw [s2Body] at hq
        cases hq⟩
    have outcome := contract.sem "loop_body" false false s2 sc cw env0 inv2 widths rc
    obtain ⟨res, invC, valCw, fvals⟩ := outcome.execution
    have resR : res rW = env0 rW := by
      apply fvals
      rw [s2Used]
      simp [Std.HashSet.contains_insert]
    have allocSt : ∀ q ∈ st.module.wires, Sparkle.IR.NameHints.Allocated q.name := by
      intro q hq
      rw [stWires] at hq
      rcases frame.wireNames q hq with hold | halloc
      · rw [s2Module, mws.2.2.2, ← hr0] at hold
        rcases List.mem_cons.mp hold with rfl | hold2
        · rw [hr0]
          exact CircuitM.makeWire_allocated "out" (.bitVector w) true _
        · exact prepare_wires_allocated bools bits (bs.zip ids) _
            (by
              rw [show (start (entryCompilerState false cache) declName.toString).state =
                CircuitM.init declName.toString from rfl, init_wires]
              intro x hx
              cases hx)
            q hold2
      · exact halloc
    have widthRst : declaredWidths st "rst" = 0 := by
      unfold Tools.ShippingMixedOutputSoundness.declaredWidths
      cases hf : st.module.wires.find? (fun q => q.name == "rst") with
      | none => simp [hf]
      | some q =>
        have hq := List.mem_of_find?_eq_some hf
        have eq : q.name = "rst" := by simpa using List.find?_some hf
        exact absurd (eq ▸ allocSt q hq) not_allocated_rst
    have seqSc : SeqBody sc.module.finalize.body := by
      intro stq hq
      obtain ⟨l, rhs, eq, _⟩ := invC.typed stq (by
        change stq ∈ sc.module.body.reverse at hq
        exact List.mem_reverse.mp hq)
      exact Or.inl ⟨l, rhs, eq⟩
    have preAssigns : ∀ stq ∈ sc.module.finalize.body, ∃ l rhs, stq = .assign l rhs := by
      intro stq hq
      obtain ⟨l, rhs, eq, _⟩ := invC.typed stq (by
        change stq ∈ sc.module.body.reverse at hq
        exact List.mem_reverse.mp hq)
      exact ⟨l, rhs, eq⟩
    have preEq : sc.module.finalize.body = sc.module.body.reverse := by
      simp [Module.finalize]
    have rstNotW : "rst" ∉ Sparkle.IR.Reorder.writesOf sc.module.finalize.body := by
      intro hwr
      obtain ⟨stq, hst, hz⟩ := List.mem_flatMap.mp hwr
      obtain ⟨l, rhs, eq, htyped⟩ := invC.typed stq (by
        rw [preEq] at hst
        exact List.mem_reverse.mp hst)
      subst eq
      simp only [Sparkle.IR.Reorder.stmtWrites, List.mem_singleton] at hz
      subst hz
      have pos := htyped.positive
      rw [widthRst] at pos
      exact Nat.lt_irrefl 0 pos
    have runsC : evalAssigns (declaredWidths st) mems sc.module.finalize.body env0 = some res :=
      invC.runs
    have resRst : res "rst" = env0 "rst" := evalAssigns_preserved seqSc runsC rstNotW
    have smUsed : sm.usedNames = sc.usedNames := by
      rw [hrec]
      show smR.usedNames = _
      rw [hsmR, hs4]
    have cwUsed : sc.usedNames.contains cw = true := outcome.used
    have cwNotOut : cw ≠ "out" := by
      intro eq
      have hmem : sm.usedNames.contains cw = true := by rw [smUsed]; exact cwUsed
      rw [eq, freshOut] at hmem
      cases hmem
    let envF : Env := fun n => if n = "out" then res rW else res n
    have evalFull : evalAssigns (declaredWidths st) mems m.body env0 = some envF := by
      rw [mBody, ← preEq, evalAssigns_append seqSc, runsC]
      show evalAssigns _ mems
        (.register rW "clk" ("rst", .asynchronous) (.ref cw) v ::
          .assign "out" (.ref rW) :: []) res = _
      simp [evalAssigns, evalExpr, envF]
    have hcwF : envF cw = (eval bvals
        (fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) e).toNat := by
      simp only [envF, if_neg cwNotOut]
      exact valCw
    have hrstF : envF "rst" = 0 := by
      have h1 : ("rst" : String) ≠ "out" := by decide
      simp only [envF, if_neg h1]
      rw [resRst, hrst0]
    have nexts : regNexts (declaredWidths st) mems m.body envF =
        some [(rW, (eval bvals
          (fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) e).toNat)] := by
      rw [mBody, ← preEq, regNexts_skip_assigns preAssigns]
      show regNexts _ mems
        (.register rW "clk" ("rst", .asynchronous) (.ref cw) v ::
          .assign "out" (.ref rW) :: []) envF = _
      have maskEq : mask (declaredWidths st rW) (eval bvals
          (fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) e).toNat =
          (eval bvals
            (fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) e).toNat := by
        rw [wR]
        exact Nat.mod_eq_of_lt (BitVec.isLt _)
      simp [regNexts, evalExpr, hcwF, hrstF, maskEq]
    have seqM : SeqBody m.body := by
      rw [mBody, ← preEq]
      intro stq hq
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (preAssigns stq hq)
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inr ⟨_, _, _, _, _, rfl⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl ⟨_, _, rfl⟩
          · cases hq
    have mem0 : memNexts (declaredWidths st) m.body mems envF = some mems := memNexts_seq seqM
    have scalarSt : ScalarWires st := by
      intro q hq
      rw [stWires] at hq
      apply frame.scalar
      · intro q2 hq2
        rw [s2Module, mws.2.2.2, ← hr0] at hq2
        rcases List.mem_cons.mp hq2 with rfl | hq2
        · exact Or.inr ⟨w, rfl⟩
        · exact (prepare_shape (bs.zip ids) _ (by
            intro q3 hq3
            rw [show (start (entryCompilerState false cache) declName.toString).state =
              CircuitM.init declName.toString from rfl, init_wires] at hq3
            cases hq3)).1 q2 hq2
      · exact hq
    have wm : weOf m = declaredWidths st := by
      rw [weOf_eq_moduleWidths (by
        intro q hq
        rw [mWires, List.mem_reverse] at hq
        exact scalarSt q hq)]
      exact moduleWidths_finish mWires wiresSt
    -- Sequential zero-width cleanup is the identity on the feedback shape too.
    have nodupM : (m.wires.map (·.name)).Nodup := by
      rw [mWires, List.map_reverse]
      exact nodup_reverse wiresSt.1
    have allocM : ∀ q ∈ m.wires, Sparkle.IR.NameHints.Allocated q.name := by
      intro q hq
      rw [mWires, List.mem_reverse] at hq
      exact allocSt q hq
    have outNotWire : "out" ∉ m.wires.map (·.name) := by
      intro hmem
      obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
      exact not_allocated_out (eq ▸ allocM q hq)
    have smWiresEq : sm.module.wires = st.module.wires := by
      rw [ht, emitAssign_wires, addOutput_state]
      rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).wires = mo.wires from
        fun _ _ => rfl]
    have wSm : declaredWidths sm rW = w := by
      unfold Tools.ShippingMixedOutputSoundness.declaredWidths
      rw [smWiresEq]
      exact wR
    have tyBW : ty.bitWidth = w := by
      rw [hty]
      unfold Tools.ShippingEntrySoundness.leafOutputType
      unfold Tools.ShippingMixedOutputSoundness.declaredWidths at wSm
      cases hf : sm.module.wires.find? (fun q => q.name == rW) with
      | none =>
        rw [hf] at wSm
        simp at wSm
        omega
      | some q =>
        rw [hf] at wSm
        simpa using wSm
    have mOutputs : m.outputs = [{ name := "out", ty := ty }] := by
      have outputsSm : sm.module.outputs = [] := by
        rw [hrec]
        show smR.module.outputs = _
        rw [hsmR, hs4]
        show (sc.module.addStmt _).outputs = _
        rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addStmt q).outputs = mo.outputs from
          fun _ _ => rfl, frame.outputs, s2Module, makeWire_outputs,
          (prepare_shape (bs.zip ids) _ (by
            intro q hq'
            rw [show (start (entryCompilerState false cache) declName.toString).state =
              CircuitM.init declName.toString from rfl, init_wires] at hq'
            cases hq')).2]
        rfl
      rw [hm]
      show ((addClockResetIfSequential st.module).finalize).outputs = _
      simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
      rw [ht, emitAssign_outputs, addOutput_state]
      simp [Module.addOutput, outputsSm]
    have wmOut : (Sparkle.IR.Optimize.buildWidthMap m).get? "out" = some w := by
      unfold Sparkle.IR.Optimize.buildWidthMap
      rw [Tools.ShippingPostSoundness.wmFold_notin m.wires _ "out" outNotWire, mOutputs]
      simp [Std.HashMap.get?_insert, tyBW]
    have hwPos : 0 < w := e.wf_pos he
    have bodyEq : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body := by
      unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
      split
      · rfl
      · show m.body.filterMap (Sparkle.IR.ZeroWidth.dzStmt (Sparkle.IR.Optimize.buildWidthMap m))
          = m.body
        apply Tools.ShippingPostSoundness.filterMap_eq_self
        intro stq hst
        rw [mBody] at hst
        rcases List.mem_append.mp hst with hpre | hrest
        · obtain ⟨l, rhs, rfl, htyped⟩ := invC.typed stq (List.mem_reverse.mp hpre)
          have hpos : 0 < weOf m l := by rw [wm]; exact htyped.positive
          have hg := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpos
          have htym : TypedExpr (weOf m) rhs (weOf m l) := by rw [wm]; exact htyped
          have hwmr : ∀ x ∈ Sparkle.IR.Reorder.refsOf rhs,
              Sparkle.IR.ZeroWidth.exprWidth (Sparkle.IR.Optimize.buildWidthMap m)
                (.ref x) ≠ 0 := by
            intro x hx
            have hpx := htym.refs_positive x hx
            have hgx := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpx
            simp only [Sparkle.IR.ZeroWidth.exprWidth, Std.HashMap.getD_eq_getD_getElem?,
              ← Std.HashMap.get?_eq_getElem?, hgx, Option.getD_some]
            omega
          rw [dzStmt_assign _ _ _ hg (by omega),
            Tools.ShippingTypedPostSoundness.dzExpr_typed htym _ hwmr]
        · rcases List.mem_cons.mp hrest with rfl | hrest
          · simp [Sparkle.IR.ZeroWidth.dzStmt, Sparkle.IR.ZeroWidth.dzExpr]
          · rcases List.mem_cons.mp hrest with rfl | hnil
            · rw [dzStmt_assign _ _ _ wmOut (by omega)]
              simp [Sparkle.IR.ZeroWidth.dzExpr]
            · cases hnil
    have weEq : weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m := by
      unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
      split
      · rfl
      · exact (weOf_congr_wires rfl).trans (Tools.ShippingPostSoundness.weOf_dropWires m nodupM)
    refine ⟨by rw [wm]; exact wR, bodyEq, weEq, envF, ?_, by simp [envF, resR]⟩
    rw [wm]
    unfold stepModule
    simp [evalFull, nexts, mem0, bind]

/-! ### Gate acceptance with the pushed loop binder -/

theorem mixed_kind_at_push {bs : List (Name × MixedGateBinder)} {j : Nat} {name kind}
    {k : MixedGateBinder} (pos : bs[j]? = some (name, kind)) :
    mixedGateBVar? ((bs.map Prod.snd).toArray.push k) (bs.length + 1 - 1 - j) = some kind := by
  have bound := (List.getElem_of_getElem? pos).choose
  unfold mixedGateBVar?
  simp only [Array.size_push, List.size_toArray, List.length_map]
  rw [if_pos (by omega)]
  have eq : bs.length + 1 - 1 - (bs.length + 1 - 1 - j) = j := by omega
  rw [eq]
  have hpush : ((bs.map Prod.snd).toArray.push k)[j]? = ((bs.map Prod.snd).toArray)[j]? := by
    rw [Array.getElem?_push]
    rw [if_neg (by simp; omega)]
  rw [hpush]
  simp [List.getElem?_map, pos]

theorem mixed_kind_self {bs : List (Name × MixedGateBinder)} {k : MixedGateBinder} :
    mixedGateBVar? ((bs.map Prod.snd).toArray.push k) 0 = some k := by
  unfold mixedGateBVar?
  simp only [Array.size_push, List.size_toArray, List.length_map]
  rw [if_pos (by omega)]
  simp

theorem input_bool_accepted_push {bs : List (Name × MixedGateBinder)} {j : Nat} {name}
    {k : MixedGateBinder} (pos : bs[j]? = some (name, .bool)) :
    unifiedGateBoolBody ((bs.map Prod.snd).toArray.push k)
      (inputExpr (bs.length + 1) j) = true := by
  change (mixedGateBVar? ((bs.map Prod.snd).toArray.push k) (bs.length + 1 - 1 - j) ==
    some MixedGateBinder.bool) = true
  rw [mixed_kind_at_push pos]
  rfl

theorem input_bits_accepted_push {bs : List (Name × MixedGateBinder)} {j : Nat} {name n}
    {k : MixedGateBinder} (pos : bs[j]? = some (name, .bits n)) :
    unifiedGateBitsBody ((bs.map Prod.snd).toArray.push k) n
      (inputExpr (bs.length + 1) j) = true := by
  change (mixedGateBVar? ((bs.map Prod.snd).toArray.push k) (bs.length + 1 - 1 - j) ==
    some (MixedGateBinder.bits n)) = true
  rw [mixed_kind_at_push pos]
  simp

theorem self_bits_accepted {bs : List (Name × MixedGateBinder)} {w : Nat} :
    unifiedGateBitsBody ((bs.map Prod.snd).toArray.push (.bits w)) w (.bvar 0) = true := by
  change (mixedGateBVar? ((bs.map Prod.snd).toArray.push (.bits w)) 0 ==
    some (MixedGateBinder.bits w)) = true
  rw [mixed_kind_self]
  simp

theorem unifiedRegisterRoot_loopRegisterE {kinds : Array MixedGateBinder}
    {domO domI inst cone : Lean.Expr} {w v : Nat}
    (hdom : (domO.isFVar || domO.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (body : unifiedGateBitsBody (kinds.push (.bits w)) w cone = true) :
    unifiedRegisterRoot kinds (loopRegisterE domO domI inst w v cone) = true := by
  unfold unifiedRegisterRoot
  have hreg : canonicalRegister? (loopRegisterE domO domI inst w v cone) = none := rfl
  have hregEn : canonicalRegisterEnable? (loopRegisterE domO domI inst w v cone) = none := rfl
  rw [hreg, hregEn, canonicalLoopRegister?_loopRegisterE hdom hw hv]
  simp [hw, body]

theorem loopRegister_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {domO domI inst : Lean.Expr} {w v : Nat} {kb kv : Nat} {vw : Nat → Nat}
    {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (peel : mixedGatePeel d.value = some (bs, loopRegisterE domO domI inst w v
      (quote domI (fun j => inputExpr (bs.length + 1) (bpos j))
        (fun j => if j = kv then .bvar 0 else inputExpr (bs.length + 1) (vpos j)) e)))
    (hdom : (domO.isFVar || domO.isBVar) = true) (hself : vw kv = w) (hv : v < 2 ^ w)
    (he : e.WF kb (kv + 1) vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∀ isInst, mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, loopRegisterE domO domI inst w v
      (quote domI (fun j => inputExpr (bs.length + 1) (bpos j))
        (fun j => if j = kv then .bvar 0 else inputExpr (bs.length + 1) (vpos j)) e)) := by
  intro isInst
  have body : unifiedGateBitsBody ((bs.map Prod.snd).toArray.push (.bits w)) w
      (quote domI (fun j => inputExpr (bs.length + 1) (bpos j))
        (fun j => if j = kv then .bvar 0 else inputExpr (bs.length + 1) (vpos j)) e) = true :=
    unified_quote_accepted
      (fun j hj => (hb j hj).elim fun name pos => input_bool_accepted_push pos)
      (fun j hj => by
        by_cases hkv : j = kv
        · subst hkv
          simp only [if_pos rfl]
          rw [hself]
          exact self_bits_accepted
        · have hjlt : j < kv := by omega
          simp only [if_neg hkv]
          exact (hvp j hjlt).elim fun name pos => input_bits_accepted_push pos)
      e he
  have root := unifiedRegisterRoot_loopRegisterE (domI := domI) (inst := inst)
    hdom (e.wf_pos he) hv body
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, Bool.or_true, Bool.true_or, if_true]

/-! ## Real-entry connection -/

theorem synthesizeFromConst_register_sound {logProf declName ci bs body m d} {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    RegisterPreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_register_sound run

/-- The raw synthesized module of the real core entry: cycle-level register
preservation for whatever register-root shape the gate accepted. -/
theorem synthesizeCombinationalCore_register_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        RegisterPreserves declName bs body m := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape =>
    synthesizeFromConst_register_sound old (shape _) (Tools.ShippingEntrySoundness.entry_kept (shape _) run).mreturns⟩

/-! ## Source-position plumbing -/

/-- Close valuation lookups and body instantiation from the source telescope,
leaving per-cycle port-value agreement (`SourceInputs`) as the premise. -/
theorem register_source {declName : Name} {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr} {m : Sparkle.IR.AST.Module} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (source : RegisterPreserves declName bs body m)
    (hbody : body = registerE (inputExpr bs.length dpos) w v
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))
    (hdp : dpos < bs.length)
    (he : e.WF kb kv vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 →
      weOf m r = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun j => bools (bpos j))
            (fun j n => bits (vpos j) n) e).toNat)], mems) ∧
        envF "out" = env0 r := by
  obtain ⟨ids, nd, len, cache, H⟩ := source
  have qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      registerE (.fvar ids[dpos]!) w v
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => .fvar ids[vpos j]!) e) := by
    rw [hbody, instFVars_registerE, instantiated_input len hdp]
    congr 1
    rw [show (Lean.Expr.fvar ids[dpos]!) =
      instFVars (ids.map Lean.Expr.fvar).toArray 0 (inputExpr bs.length dpos) from
      (instantiated_input len hdp).symm]
    apply instantiated_quote _ _ e he
    · intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
    · intro j hj
      obtain ⟨name, pos⟩ := hvp j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
  obtain ⟨r, H⟩ := H (.fvar ids[dpos]!) kb kv vw (fun j => ids[bpos j]!)
    (fun j => ids[vpos j]!) e (by rfl) he hvlt qeq
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro bools bits env0 mems values hrst0
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  apply H (boolValues ids bools) (bitValues ids bits) env0 mems
    (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) values _ _ hrst0
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bool_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup
  · intro j hj
    obtain ⟨name, pos⟩ := hvp j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup

/-- General register endpoint at the real core entry: for the raw synthesized
module of `synthesizeCombinationalCore` (the `SPARKLE_NO_REGDEDUP=1`
configuration before zero-width cleanup), every cycle with admissible inputs
and reset low observes the current register value on `out` and steps the
register by the source term's value. Iterate with `trace_of_cycles` for the
full `runModule` trace. -/
theorem register_step_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, registerE (inputExpr bs.length dpos) w v
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e)))
    (hdp : dpos < bs.length)
    (he : e.WF kb kv vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 →
      weOf m r = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun j => bools (bpos j))
            (fun j n => bits (vpos j) n) e).toNat)], mems) ∧
        envF "out" = env0 r := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_register_sound hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have hdom : ((inputExpr bs.length dpos).isFVar || (inputExpr bs.length dpos).isBVar) = true := by
    simp only [Tools.ShippingMixedSourceBridge.inputExpr]
    rfl
  have mixedGate := register_term_gate (d := d)
    (by rw [definition]; exact peel) hdom hvlt he hb hvp
  exact register_source (source bs _ oldGate mixedGate) rfl hdp he hvlt hb hvp

theorem synthesizeFromConst_registerEnable_sound {logProf declName ci bs body m d} {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    RegisterEnablePreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_registerEnable_sound run

theorem synthesizeCombinationalCore_registerEnable_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        RegisterEnablePreserves declName bs body m := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape =>
    synthesizeFromConst_registerEnable_sound old (shape _) (Tools.ShippingEntrySoundness.entry_kept (shape _) run).mreturns⟩

/-- Position plumbing for the enabled register root. -/
theorem registerEnable_source {declName : Name} {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr} {m : Sparkle.IR.AST.Module} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {en : Term .bool} {e : Term (.bits w)}
    (source : RegisterEnablePreserves declName bs body m)
    (hbody : body = registerEnableE (inputExpr bs.length dpos) w v
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) en)
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))
    (hdp : dpos < bs.length)
    (hen : en.WF kb kv vw) (he : e.WF kb kv vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ w →
      weOf m r = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, if eval (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) en
            then (eval (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) e).toNat
            else env0 r)], mems) ∧
        envF "out" = env0 r := by
  obtain ⟨ids, nd, len, cache, H⟩ := source
  have qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      registerEnableE (.fvar ids[dpos]!) w v
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => .fvar ids[vpos j]!) en)
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => .fvar ids[vpos j]!) e) := by
    rw [hbody, instFVars_registerEnableE, instantiated_input len hdp]
    rw [show (Lean.Expr.fvar ids[dpos]!) =
      instFVars (ids.map Lean.Expr.fvar).toArray 0 (inputExpr bs.length dpos) from
      (instantiated_input len hdp).symm]
    congr 1
    · apply instantiated_quote _ _ en hen
      · intro j hj
        obtain ⟨name, pos⟩ := hb j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose
      · intro j hj
        obtain ⟨name, pos⟩ := hvp j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose
    · apply instantiated_quote _ _ e he
      · intro j hj
        obtain ⟨name, pos⟩ := hb j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose
      · intro j hj
        obtain ⟨name, pos⟩ := hvp j hj
        exact instantiated_input len (List.getElem_of_getElem? pos).choose
  obtain ⟨r, H⟩ := H (.fvar ids[dpos]!) kb kv vw (fun j => ids[bpos j]!)
    (fun j => ids[vpos j]!) en e (by rfl) hen he hvlt qeq
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro bools bits env0 mems values hrst0 hstb
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  apply H (boolValues ids bools) (bitValues ids bits) env0 mems
    (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) values _ _ hrst0 hstb
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bool_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup
  · intro j hj
    obtain ⟨name, pos⟩ := hvp j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup

/-- General enabled-register endpoint at the real core entry: each cycle with
admissible inputs, reset low and a width-bounded register seed observes the
current value on `out` and updates by the enable/hold recurrence. -/
theorem registerEnable_step_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {en : Term .bool} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, registerEnableE (inputExpr bs.length dpos) w v
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) en)
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e)))
    (hdp : dpos < bs.length)
    (hen : en.WF kb kv vw) (he : e.WF kb kv vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ w →
      weOf m r = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, if eval (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) en
            then (eval (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) e).toNat
            else env0 r)], mems) ∧
        envF "out" = env0 r := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_registerEnable_sound hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have hdom : ((inputExpr bs.length dpos).isFVar || (inputExpr bs.length dpos).isBVar) = true := by
    simp only [Tools.ShippingMixedSourceBridge.inputExpr]
    rfl
  have mixedGate := registerEnable_term_gate (d := d)
    (by rw [definition]; exact peel) hdom hvlt hen he hb hvp
  exact registerEnable_source (source bs _ oldGate mixedGate) rfl hdp hen he hvlt hb hvp

theorem synthesizeFromConst_loopRegister_sound {logProf declName ci bs body m d} {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    LoopRegisterPreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_loopRegister_sound run

theorem synthesizeCombinationalCore_loopRegister_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        LoopRegisterPreserves declName bs body m := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape =>
    synthesizeFromConst_loopRegister_sound old (shape _) (Tools.ShippingEntrySoundness.entry_kept (shape _) run).mreturns⟩

/-- Instantiation of the shifted telescope under the loop binder. -/
theorem instantiated_input_shift {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    (len : ids.length = bs.length) {j : Nat} (hj : j < bs.length) :
    instFVars (ids.map Lean.Expr.fvar).toArray 1 (inputExpr (bs.length + 1) j) =
      .fvar ids[j]! := by
  simp only [Tools.ShippingMixedSourceBridge.inputExpr, instFVars,
    List.size_toArray, List.length_map]
  rw [if_neg (by omega), if_pos (by omega)]
  have eq : ids.length - 1 - (bs.length + 1 - 1 - j - 1) = j := by omega
  rw [eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by omega : j < ids.length)]

/-- Position plumbing for the feedback register root. -/
theorem loopRegister_source {declName : Name} {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr} {m : Sparkle.IR.AST.Module} {instE : Lean.Expr} {dpos : Nat}
    {w v kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (source : LoopRegisterPreserves declName bs body m)
    (hbody : body = loopRegisterE (inputExpr bs.length dpos) (inputExpr (bs.length + 1) dpos)
      instE w v
      (quote (inputExpr (bs.length + 1) dpos) (fun j => inputExpr (bs.length + 1) (bpos j))
        (fun j => if j = kv then .bvar 0 else inputExpr (bs.length + 1) (vpos j)) e))
    (hdp : dpos < bs.length)
    (hself : vw kv = w) (he : e.WF kb (kv + 1) vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ w →
      weOf m r = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun j => bools (bpos j))
            (fun j n => if j = kv then BitVec.ofNat n (env0 r) else bits (vpos j) n)
            e).toNat)], mems) ∧
        envF "out" = env0 r := by
  obtain ⟨ids, nd, len, cache, H⟩ := source
  have qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      loopRegisterE (.fvar ids[dpos]!) (.fvar ids[dpos]!)
        (instFVars (ids.map Lean.Expr.fvar).toArray 0 instE) w v
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => if j = kv then .bvar 0 else .fvar ids[vpos j]!) e) := by
    rw [hbody, instFVars_loopRegisterE, instantiated_input len hdp,
      instantiated_input_shift len hdp]
    congr 1
    rw [show (Lean.Expr.fvar ids[dpos]!) =
      instFVars (ids.map Lean.Expr.fvar).toArray 1 (inputExpr (bs.length + 1) dpos) from
      (instantiated_input_shift len hdp).symm]
    rw [instFVars_quote]
    apply quote_congr _ _ e he
    · intro j hj
      exact instantiated_input_shift len (List.getElem_of_getElem? (hb j hj).choose_spec).choose
    · intro j hj
      by_cases hkv : j = kv
      · subst hkv
        simp only [if_pos rfl]
        rfl
      · have hjlt : j < kv := by omega
        simp only [if_neg hkv]
        exact instantiated_input_shift len
          (List.getElem_of_getElem? (hvp j hjlt).choose_spec).choose
  obtain ⟨r, H⟩ := H (.fvar ids[dpos]!) (.fvar ids[dpos]!)
    (instFVars (ids.map Lean.Expr.fvar).toArray 0 instE) kb kv vw
    (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) e (by rfl) hself he hvlt qeq
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro bools bits env0 mems values hrst0 hstb
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  apply H (boolValues ids bools) (bitValues ids bits) env0 mems
    (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) values _ _ hrst0 hstb
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bool_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup
  · intro j hj
    obtain ⟨name, pos⟩ := hvp j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup

/-- General feedback-register endpoint at the real core entry. -/
theorem loopRegister_step_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value instE : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, loopRegisterE (inputExpr bs.length dpos)
      (inputExpr (bs.length + 1) dpos) instE w v
      (quote (inputExpr (bs.length + 1) dpos) (fun j => inputExpr (bs.length + 1) (bpos j))
        (fun j => if j = kv then .bvar 0 else inputExpr (bs.length + 1) (vpos j)) e)))
    (hdp : dpos < bs.length)
    (hself : vw kv = w) (he : e.WF kb (kv + 1) vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ w →
      weOf m r = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun j => bools (bpos j))
            (fun j n => if j = kv then BitVec.ofNat n (env0 r) else bits (vpos j) n)
            e).toNat)], mems) ∧
        envF "out" = env0 r := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_loopRegister_sound hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have hdom : ((inputExpr bs.length dpos).isFVar || (inputExpr bs.length dpos).isBVar) = true := by
    simp only [Tools.ShippingMixedSourceBridge.inputExpr]
    rfl
  have mixedGate := loopRegister_term_gate (d := d)
    (by rw [definition]; exact peel) hdom hself hvlt he hb hvp
  exact loopRegister_source (source bs _ oldGate mixedGate) rfl hdp hself he hvlt hb hvp

/-! ## Trace iteration -/

/-- Invariant-carrying trace iteration: the per-cycle step is available only
at states satisfying `P` (e.g. width-boundedness for the hold/feedback
paths), and the update preserves `P`. -/
theorem trace_of_cycles_inv {we : WEnv} {body : List Stmt} {r : String} {mems : MEnv}
    {seed : Nat → (String → Nat) → Env} {F : Nat → Nat → Nat} {P : Nat → Prop}
    (step : ∀ t stv, P (stv r) → ∃ envF,
      stepModule we body (seed t stv) mems = some (envF, [(r, F t (stv r))], mems) ∧
      envF "out" = stv r)
    (Pstep : ∀ t s, P s → P (F t s)) :
    ∀ (k : Nat) (st0 : String → Nat) (S : Nat → Nat), P (st0 r) →
      S 0 = st0 r → (∀ j, j + 1 ≤ k → S (j + 1) = F (k - 1 - j) (S j)) →
      ∃ envs, runModule we body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j
  | 0, st0, S, _, hS0, hSs => ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, st0, S, P0, hS0, hSs => by
    obtain ⟨envF, hstep, hout⟩ := step k st0 P0
    have hnext : applyNexts st0 [(r, F k (st0 r))] r = F k (st0 r) := by
      simp [applyNexts]
    obtain ⟨rest, hrun, hlen, hobs⟩ := trace_of_cycles_inv step Pstep k
      (applyNexts st0 [(r, F k (st0 r))]) (fun j => S (j + 1))
      (by rw [hnext]; exact Pstep k (st0 r) P0)
      (by
        show S (0 + 1) = _
        rw [hnext, hSs 0 (by omega), hS0]
        simp)
      (by
        intro j hj
        show S (j + 1 + 1) = F (k - 1 - j) (S (j + 1))
        rw [hSs (j + 1) (by omega)]
        have hidx : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
        rw [hidx])
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj
      cases j with
      | zero => rw [hS0]; simpa using hout
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget]
        exact hobs i hi

/-- The feedback loop's stream: at 0 the register initializes; afterwards the
cone observes the loop itself one tick earlier. The cone only needs to be
pointwise in its argument (true of every combinational denotation). -/
theorem loop_register_val {D : Sparkle.Core.Domain.DomainConfig} {w : Nat} (init : BitVec w)
    (cone : Sparkle.Core.Signal.Signal D (BitVec w) →
      Sparkle.Core.Signal.Signal D (BitVec w))
    (hcone : ∀ (s₁ s₂ : Sparkle.Core.Signal.Signal D (BitVec w)) (t : Nat),
      s₁.val t = s₂.val t → (cone s₁).val t = (cone s₂).val t) :
    ((Sparkle.Core.Signal.Signal.loop
        (fun s => Sparkle.Core.Signal.Signal.register init (cone s))).val 0 = init) ∧
    ∀ t, (Sparkle.Core.Signal.Signal.loop
        (fun s => Sparkle.Core.Signal.Signal.register init (cone s))).val (t + 1) =
      (cone (Sparkle.Core.Signal.Signal.loop
        (fun s => Sparkle.Core.Signal.Signal.register init (cone s)))).val t := by
  constructor
  · show Sparkle.Core.Signal.Signal.loopGo _ 0 = init
    rw [Sparkle.Core.Signal.Signal.loopGo_eq]
    rfl
  · intro t
    show Sparkle.Core.Signal.Signal.loopGo _ (t + 1) = _
    rw [Sparkle.Core.Signal.Signal.loopGo_eq]
    show (cone ⟨fun i => if i < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ i else default⟩).val t = _
    apply hcone
    show (if t < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ t else default) = _
    rw [if_pos (by omega)]
    rfl

/-- Iterating the per-cycle property along `runModule`: cycle `j` (wall
clock, oldest first) observes the state sequence `S`, which follows the
recurrence `S 0 = st0 r`, `S (j+1) = F (k-1-j) (S j)` (`runModule`'s seed
index counts down; the update may read the current state, covering the
enabled register's hold path). -/
theorem trace_of_cycles {we : WEnv} {body : List Stmt} {r : String} {mems : MEnv}
    {seed : Nat → (String → Nat) → Env} {F : Nat → Nat → Nat}
    (step : ∀ t stv, ∃ envF,
      stepModule we body (seed t stv) mems = some (envF, [(r, F t (stv r))], mems) ∧
      envF "out" = stv r) :
    ∀ (k : Nat) (st0 : String → Nat) (S : Nat → Nat),
      S 0 = st0 r → (∀ j, j + 1 ≤ k → S (j + 1) = F (k - 1 - j) (S j)) →
      ∃ envs, runModule we body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j
  | 0, st0, S, hS0, hSs => ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, st0, S, hS0, hSs => by
    obtain ⟨envF, hstep, hout⟩ := step k st0
    have hnext : applyNexts st0 [(r, F k (st0 r))] r = F k (st0 r) := by
      simp [applyNexts]
    obtain ⟨rest, hrun, hlen, hobs⟩ := trace_of_cycles step k
      (applyNexts st0 [(r, F k (st0 r))]) (fun j => S (j + 1))
      (by
        show S (0 + 1) = _
        rw [hnext, hSs 0 (by omega), hS0]
        simp)
      (by
        intro j hj
        show S (j + 1 + 1) = F (k - 1 - j) (S (j + 1))
        rw [hSs (j + 1) (by omega)]
        have hidx : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
        rw [hidx])
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj
      cases j with
      | zero => rw [hS0]; simpa using hout
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget]
        exact hobs i hi

/-- Packaged feedback trace at the real core entry: for every admissible
per-cycle seeding discipline (inputs at the wall-clock cycle, reset low, the
register wire reading the threaded state), the compiled module's `runModule`
trace observes exactly the state sequence of the source recurrence
`S 0 = st0 r`, `S (j+1) = cone(inputs_j, self := S j)` — the
`Signal.loop`/`Signal.register` fixpoint stream (see `loop_register_val`). -/
theorem loopRegister_run_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value instE : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, loopRegisterE (inputExpr bs.length dpos)
      (inputExpr (bs.length + 1) dpos) instE w v
      (quote (inputExpr (bs.length + 1) dpos) (fun j => inputExpr (bs.length + 1) (bpos j))
        (fun j => if j = kv then .bvar 0 else inputExpr (bs.length + 1) (vpos j)) e)))
    (hdp : dpos < bs.length)
    (hself : vw kv = w) (he : e.WF kb (kv + 1) vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Nat → Bool) (bits : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat) (S : Nat → Nat),
      (∀ t stv, SourceInputs declName bs ids cache (bools (k - 1 - t)) (bits (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r < 2 ^ w →
      S 0 = st0 r →
      (∀ j, j + 1 ≤ k → S (j + 1) = (eval (fun i => bools j (bpos i))
        (fun i n => if i = kv then BitVec.ofNat n (S j) else bits j (vpos i) n) e).toNat) →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j := by
  obtain ⟨ids, nd, len, cache, r, H⟩ :=
    loopRegister_step_of_env hr env old peel hdp hself he hvlt hb hvp
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro bools bits mems k seed st0 S hseed hst0 hS0 hSs
  apply trace_of_cycles_inv (P := fun s => s < 2 ^ w)
    (F := fun t s => (eval (fun i => bools (k - 1 - t) (bpos i))
      (fun i n => if i = kv then BitVec.ofNat n s else bits (k - 1 - t) (vpos i) n) e).toNat)
    ?_ ?_ k st0 S hst0 hS0 ?_
  · intro t stv hP
    obtain ⟨hsrc, hrst, hread⟩ := hseed t stv
    obtain ⟨-, -, -, envF, hstep, hout⟩ :=
      H (bools (k - 1 - t)) (bits (k - 1 - t)) (seed t stv) mems hsrc hrst
        (by rw [hread]; exact hP)
    refine ⟨envF, ?_, by rw [hout, hread]⟩
    rw [hread] at hstep
    exact hstep
  · intro t s hP
    exact BitVec.isLt _
  · intro j hj
    rw [hSs j hj]
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    rw [hidx]


/-- The enabled register's stream, exposed as its defining recurrence. -/
theorem registerWithEnable_val {D : Sparkle.Core.Domain.DomainConfig} {α : Type}
    (init : α) (en : Sparkle.Core.Signal.Signal D Bool)
    (input : Sparkle.Core.Signal.Signal D α) :
    ((Sparkle.Core.Signal.Signal.registerWithEnable init en input).val 0 = init) ∧
    ∀ t, (Sparkle.Core.Signal.Signal.registerWithEnable init en input).val (t + 1) =
      if en.val t then input.val t
      else (Sparkle.Core.Signal.Signal.registerWithEnable init en input).val t :=
  ⟨rfl, fun _ => rfl⟩

/-- Packaged plain-register trace at the real core entry: the `runModule`
trace observes the source register stream (state 0 from the declared init,
then the cone at the previous cycle's inputs). -/
theorem register_run_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, registerE (inputExpr bs.length dpos) w v
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e)))
    (hdp : dpos < bs.length)
    (he : e.WF kb kv vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Nat → Bool) (bits : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat) (S : Nat → Nat),
      (∀ t stv, SourceInputs declName bs ids cache (bools (k - 1 - t)) (bits (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      S 0 = st0 r →
      (∀ j, j + 1 ≤ k → S (j + 1) = (eval (fun i => bools j (bpos i))
        (fun i n => bits j (vpos i) n) e).toNat) →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j := by
  obtain ⟨ids, nd, len, cache, r, H⟩ :=
    register_step_of_env hr env old peel hdp he hvlt hb hvp
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro bools bits mems k seed st0 S hseed hS0 hSs
  apply trace_of_cycles
    (F := fun t _ => (eval (fun i => bools (k - 1 - t) (bpos i))
      (fun i n => bits (k - 1 - t) (vpos i) n) e).toNat)
    ?_ k st0 S hS0 ?_
  · intro t stv
    obtain ⟨hsrc, hrst, hread⟩ := hseed t stv
    obtain ⟨-, -, -, envF, hstep, hout⟩ :=
      H (bools (k - 1 - t)) (bits (k - 1 - t)) (seed t stv) mems hsrc hrst
    exact ⟨envF, hstep, by rw [hout, hread]⟩
  · intro j hj
    rw [hSs j hj]
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    rw [hidx]

/-- Packaged enabled-register trace at the real core entry: the `runModule`
trace observes the source capture/hold stream. -/
theorem registerEnable_run_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {en : Term .bool} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, registerEnableE (inputExpr bs.length dpos) w v
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) en)
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e)))
    (hdp : dpos < bs.length)
    (hen : en.WF kb kv vw) (he : e.WF kb kv vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Nat → Bool) (bits : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat) (S : Nat → Nat),
      (∀ t stv, SourceInputs declName bs ids cache (bools (k - 1 - t)) (bits (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r < 2 ^ w →
      S 0 = st0 r →
      (∀ j, j + 1 ≤ k → S (j + 1) =
        (if eval (fun i => bools j (bpos i)) (fun i n => bits j (vpos i) n) en
          then (eval (fun i => bools j (bpos i)) (fun i n => bits j (vpos i) n) e).toNat
          else S j)) →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j := by
  obtain ⟨ids, nd, len, cache, r, H⟩ :=
    registerEnable_step_of_env hr env old peel hdp hen he hvlt hb hvp
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro bools bits mems k seed st0 S hseed hst0 hS0 hSs
  apply trace_of_cycles_inv (P := fun s => s < 2 ^ w)
    (F := fun t s => if eval (fun i => bools (k - 1 - t) (bpos i))
        (fun i n => bits (k - 1 - t) (vpos i) n) en
      then (eval (fun i => bools (k - 1 - t) (bpos i))
        (fun i n => bits (k - 1 - t) (vpos i) n) e).toNat
      else s)
    ?_ ?_ k st0 S hst0 hS0 ?_
  · intro t stv hP
    obtain ⟨hsrc, hrst, hread⟩ := hseed t stv
    obtain ⟨-, -, -, envF, hstep, hout⟩ :=
      H (bools (k - 1 - t)) (bits (k - 1 - t)) (seed t stv) mems hsrc hrst
        (by rw [hread]; exact hP)
    refine ⟨envF, ?_, by rw [hout, hread]⟩
    rw [hread] at hstep
    exact hstep
  · intro t s hP
    by_cases hEn : eval (fun i => bools (k - 1 - t) (bpos i))
        (fun i n => bits (k - 1 - t) (vpos i) n) en
    · simp only [hEn, if_true]
      exact BitVec.isLt _
    · simp only [hEn, if_false]
      exact hP
  · intro j hj
    rw [hSs j hj]
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    rw [hidx]

/-! ## The cascaded (two-stage) register root -/

theorem unifiedRegisterRoot_register2E {kinds : Array MixedGateBinder} {dom a : Lean.Expr}
    {w v1 v2 : Nat} (hdom : (dom.isFVar || dom.isBVar) = true) (hw : 0 < w)
    (hv1 : v1 < 2 ^ w) (hv2 : v2 < 2 ^ w)
    (body : unifiedGateBitsBody kinds w a = true) :
    unifiedRegisterRoot kinds (registerE dom w v1 (registerE dom w v2 a)) = true := by
  unfold unifiedRegisterRoot
  simp only [canonicalRegister?_registerE hdom hw hv1,
    canonicalRegister?_registerE hdom hw hv2]
  simp [hw, body]

/-- Once the real declaration has been peeled to a two-stage register chain
over a quoted unified source, the shipping gate accepts it. -/
theorem register2_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {w v1 v2 : Nat} {kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {e : Term (.bits w)}
    (peel : mixedGatePeel d.value = some (bs, registerE dom w v1 (registerE dom w v2
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))))
    (hdom : (dom.isFVar || dom.isBVar) = true) (hv1 : v1 < 2 ^ w) (hv2 : v2 < 2 ^ w)
    (he : e.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∀ isInst, mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, registerE dom w v1 (registerE dom w v2
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e))) := by
  intro isInst
  have body : unifiedGateBitsBody (bs.map Prod.snd).toArray w
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) = true :=
    unified_quote_accepted
      (fun j hj => (hb j hj).elim fun name pos => input_bool_accepted pos)
      (fun j hj => (hvp j hj).elim fun name pos => input_bits_accepted pos) e he
  have root := unifiedRegisterRoot_register2E hdom (e.wf_pos he) hv1 hv2 body
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, Bool.or_true, Bool.true_or, if_true]

/-- Preservation contract for the two-stage shift chain: the raw synthesized
module carries two register statements; each cycle with reset low observes
the outer register on `out`, shifts the inner register's value into the
outer one, and steps the inner register by the source cone's value. -/
def Register2Preserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (binp vinp : Nat → FVarId)
      {w v1 v2 : Nat} (e : Term (.bits w)),
    (dom.isFVar || dom.isBVar) = true → e.WF kb kv vw → v1 < 2 ^ w → v2 < 2 ^ w →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      registerE dom w v1 (registerE dom w v2
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)) →
    ∃ r1 r2 : String, r1 ≠ r2 ∧
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (mems : MEnv)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (n : Nat) → BitVec n),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨vw j, vvals j (vw j)⟩) →
    env0 "rst" = 0 → env0 r2 < 2 ^ w →
    weOf m r1 = w ∧ weOf m r2 = w ∧
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
    weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
    ∃ envF, stepModule (weOf m) m.body env0 mems =
        some (envF, [(r2, (eval bvals vvals e).toNat), (r1, env0 r2)], mems) ∧
      envF "out" = env0 r1

set_option maxHeartbeats 2000000 in
theorem synthesizeMixedCertified_register2_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    Register2Preserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, _⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw binp vinp w v1 v2 e hdom he hv1 hv2 qeq
  -- Decompose the returned translation once; this is valuation-independent.
  have leaf := prepare_returns (bs.zip ids) (start (entryCompilerState false cache) declName.toString) (bools := fun _ => false)
    (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨rW, sm, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  -- Unfold one step of the fuel fixpoint at the outer register.
  have stepEq : translateExprToWire (registerE dom w v1 (registerE dom w v2
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e))) "out" false true =
      translateControlCachedWith (translateRegisterUncachedWith
          (translateFuelFix translateStep 1048575) w v1)
        (registerE dom w v1 (registerE dom w v2
          (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e))) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (registerE dom w v1 (registerE dom w v2
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e))) "out" false true = _
    rw [register_step _ dom _ w v1 hdom (e.wf_pos he) hv1]
  rw [stepEq] at tr
  -- The prepared entry state has an empty record: both validated hits are dead.
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec rW rfl
    rw [record0] at dead
    simp at dead
  rw [registerUncached_registerE] at missRun
  obtain ⟨cw, si, rcO, remit⟩ := Returns.bind missRun
  -- Unfold one more step of the fuel fixpoint at the inner register.
  have stepEq2 : translateFuelFix translateStep 1048575 (registerE dom w v2
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)) "reg_in" false false =
      translateControlCachedWith (translateRegisterUncachedWith
          (translateFuelFix translateStep 1048574) w v2)
        (registerE dom w v2
          (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)) "reg_in" false false := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048574)
      (registerE dom w v2
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) e)) "reg_in" false false = _
    rw [register_step _ dom _ w v2 hdom (e.wf_pos he) hv2]
  rw [stepEq2] at rcO
  rcases translateControlCachedWith_returns rcO with hit2 | ⟨si', missRun2, record2⟩
  · obtain ⟨-, hrec2⟩ := cacheLookupValidated_returns hit2
    have dead := hrec2 cw rfl
    rw [record0] at dead
    simp at dead
  rw [registerUncached_registerE] at missRun2
  obtain ⟨cw2, sc, rc, remit2⟩ := Returns.bind missRun2
  obtain ⟨hCw, hsi'⟩ := emitRegister_returns remit2
  have hrec2 := recordTranslation_returns record2
  obtain ⟨hrE1i, hrE2i⟩ :=
    emitRegisterC_spec "reg_in" "clk" "rst" (.ref cw2) v2 (.bitVector w) false .asynchronous sc
  have mwsI := CircuitM.makeWire_spec "reg_in" (.bitVector w) false sc
  have hCwm : cw = (CircuitM.makeWire "reg_in" (.bitVector w) false sc).1 := hCw.trans hrE1i
  have siModule : si.module = ((CircuitM.makeWire "reg_in" (.bitVector w) false sc).2.module.addStmt
      (.register (CircuitM.makeWire "reg_in" (.bitVector w) false sc).1 "clk"
        ("rst", .asynchronous) (.ref cw2) v2)) := by
    rw [hrec2, hsi', hrE2i]
  have siUsed : si.usedNames = (CircuitM.makeWire "reg_in" (.bitVector w) false sc).2.usedNames := by
    rw [hrec2, hsi', hrE2i]
  have siBindings : si.sourceBindings = sc.sourceBindings := by
    rw [hrec2, hsi', hrE2i]
    show (CircuitM.makeWire "reg_in" (.bitVector w) false sc).2.sourceBindings = _
    exact CircuitM.makeWire_sourceBindings _ _ _ _
  -- The outer register's emission on top of the inner state.
  obtain ⟨hrW, hsmR⟩ := emitRegister_returns remit
  have hrec := recordTranslation_returns record
  obtain ⟨hrE1o, hrE2o⟩ :=
    emitRegisterC_spec "out" "clk" "rst" (.ref cw) v1 (.bitVector w) true .asynchronous si
  have mwsO := CircuitM.makeWire_spec "out" (.bitVector w) true si
  have hrWm : rW = (CircuitM.makeWire "out" (.bitVector w) true si).1 := hrW.trans hrE1o
  have smModule : sm.module = ((CircuitM.makeWire "out" (.bitVector w) true si).2.module.addStmt
      (.register (CircuitM.makeWire "out" (.bitVector w) true si).1 "clk"
        ("rst", .asynchronous) (.ref cw) v1)) := by
    rw [hrec, hsmR, hrE2o]
  have smUsed : sm.usedNames = (CircuitM.makeWire "out" (.bitVector w) true si).2.usedNames := by
    rw [hrec, hsmR, hrE2o]
  -- Static shapes of the final translation state and the finished module.
  have siBody : si.module.body =
      .register cw "clk" ("rst", .asynchronous) (.ref cw2) v2 :: sc.module.body := by
    rw [siModule]
    show _ :: (CircuitM.makeWire "reg_in" (.bitVector w) false sc).2.module.body = _
    rw [mwsI.2.2.1, ← hCwm]
  have siWires : si.module.wires = { name := cw, ty := .bitVector w } :: sc.module.wires := by
    rw [siModule]
    show (CircuitM.makeWire "reg_in" (.bitVector w) false sc).2.module.wires = _
    rw [mwsI.2.2.2, ← hCwm]
  have stBody : st.module.body =
      .assign "out" (.ref rW) :: .register rW "clk" ("rst", .asynchronous) (.ref cw) v1
        :: si.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state]
    show _ :: (sm.module.addOutput _).body = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) p, (mo.addOutput p).body = mo.body from
      fun _ _ => rfl, smModule]
    show _ :: (_ :: (CircuitM.makeWire "out" (.bitVector w) true si).2.module.body) = _
    rw [mwsO.2.2.1, ← hrWm]
  have stWires : st.module.wires = { name := rW, ty := .bitVector w } :: si.module.wires := by
    rw [ht, emitAssign_wires, addOutput_state]
    show (sm.module.addOutput _).wires = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) p, (mo.addOutput p).wires = mo.wires from
      fun _ _ => rfl, smModule]
    show (CircuitM.makeWire "out" (.bitVector w) true si).2.module.wires = _
    rw [mwsO.2.2.2, ← hrWm]
  have freshCw : sc.usedNames.contains cw = false := by rw [hCwm]; exact mwsI.1
  have cwUsedSi : si.usedNames.contains cw = true := by
    rw [siUsed, mwsI.2.1, ← hCwm]
    simp [Std.HashSet.contains_insert]
  have freshRW : si.usedNames.contains rW = false := by rw [hrWm]; exact mwsO.1
  have hne : rW ≠ cw := by
    intro eq
    rw [eq, cwUsedSi] at freshRW
    cases freshRW
  have freshRWsc : sc.usedNames.contains rW = false := by
    cases h : sc.usedNames.contains rW
    · rfl
    · exfalso
      have hmem : si.usedNames.contains rW = true := by
        rw [siUsed, mwsI.2.1, ← hCwm]
        simp [Std.HashSet.contains_insert, h]
      rw [hmem] at freshRW
      cases freshRW
  have mBody : m.body = sc.module.body.reverse ++
      [.register cw "clk" ("rst", .asynchronous) (.ref cw2) v2,
       .register rW "clk" ("rst", .asynchronous) (.ref cw) v1, .assign "out" (.ref rW)] := by
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).body = _
    simp only [Module.finalize, (addClockReset_facts st.module).1, stBody, siBody]
    simp
  have mWires : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  refine ⟨rW, cw, hne, ?_⟩
  intro bools bits env0 mems bvals vvals a p adm hb0 hv0 hrst0 hr2lt
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids) (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [pc, ps] at rc
  have hb' : ∀ j, j < kb →
      inputValues (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits (binp j) =
        some (.bool (bvals j)) :=
    fun j hj => inputValues_bool (hb0 j hj)
  have separate := prepared.1.separate prepared.2.1
  have hv' : ∀ j, j < kv →
      inputValues (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits (vinp j) =
        some (.bits (vw j) (vvals j (vw j))) :=
    fun j hj => inputValues_bits separate (hv0 j hj)
  have contract := fuel_contract 1048574 (ctx := (prepare bools bits (bs.zip ids) (start (entryCompilerState false cache) declName.toString)).context) (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' e he
  have lookup := lookup_of_ports prepared.1 prepared.2.1
  have frame := contract.frame "reg_in" false false _ sc cw2 lookup rc
  have wiresSc : WiresOk sc := frame.wires prepared.2.1
  have cwNotSc : cw ∉ sc.module.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    have := wiresSc.2 q hq
    rw [eq, freshCw] at this
    cases this
  have wiresSi : WiresOk si := by
    constructor
    · rw [siWires]
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨cwNotSc, wiresSc.1⟩
    · intro q hq
      rw [siWires] at hq
      rw [siUsed, mwsI.2.1, ← hCwm]
      rcases List.mem_cons.mp hq with rfl | hq
      · simp [Std.HashSet.contains_insert]
      · have := wiresSc.2 q hq
        simp [Std.HashSet.contains_insert, this]
  have rWNotSi : rW ∉ si.module.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    have := wiresSi.2 q hq
    rw [eq, freshRW] at this
    cases this
  have stUsed : st.usedNames = ((si.usedNames.insert rW).insert "out") := by
    rw [ht, emitAssign_usedNames, addOutput_state]
    show (sm.usedNames.insert "out") = _
    rw [smUsed, mwsO.2.1, ← hrWm]
  have wiresSt : WiresOk st := by
    constructor
    · rw [stWires]
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨rWNotSi, wiresSi.1⟩
    · intro q hq
      rw [stWires] at hq
      rw [stUsed]
      rcases List.mem_cons.mp hq with rfl | hq
      · simp [Std.HashSet.contains_insert]
      · have := wiresSi.2 q hq
        simp [Std.HashSet.contains_insert, this]
  -- Every wire name is allocated; "rst" and "out" therefore have width 0.
  have allocSt : ∀ q ∈ st.module.wires, Sparkle.IR.NameHints.Allocated q.name := by
    intro q hq
    rw [stWires] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · rw [hrWm]; exact CircuitM.makeWire_allocated "out" (.bitVector w) true si
    · rw [siWires] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · rw [hCwm]; exact CircuitM.makeWire_allocated "reg_in" (.bitVector w) false sc
      · rcases frame.wireNames q hq with hold | halloc
        · exact prepare_wires_allocated bools bits (bs.zip ids) _
            (by rw [show (start (entryCompilerState false cache) declName.toString).state =
                CircuitM.init declName.toString from rfl, init_wires]; intro x hx; cases hx)
            q hold
        · exact halloc
  have widthRst : declaredWidths st "rst" = 0 := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    cases hf : st.module.wires.find? (fun p => p.name == "rst") with
    | none => simp [hf]
    | some q =>
      have hq := List.mem_of_find?_eq_some hf
      have eq : q.name = "rst" := by simpa using List.find?_some hf
      exact absurd (eq ▸ allocSt q hq) not_allocated_rst
  -- Run the cone once at this cycle's seed.
  have widths : ScalarWidthsAgree (declaredWidths st) sc := by
    intro q hq
    exact declaredWidths_agree wiresSt q
      (by rw [stWires, siWires]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq))
  have inv0 : Inv _ (inputValues _ _) (declaredWidths st) mems env0 _ env0 :=
    initial_unified
      (by rw [prepared.2.2.1]; rfl)
      (by rw [prepared.2.2.2]; rfl)
      separate
      (prepared.1.inputs prepared.2.1
        (by intro q hq; rw [stWires, siWires]
            exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (frame.decls q hq)))
        (declaredWidths_agree wiresSt))
  have outcome := contract.sem "reg_in" false false _ sc cw2 env0 inv0 widths rc
  obtain ⟨res, invC, valCw2, frameVals⟩ := outcome.execution
  have ordered := fuel_orders 1048574 (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' e he "reg_in" false _ sc cw2 env0 rc inv0 widths
    (OrderInv.empty (by rw [prepared.2.2.1]; rfl))
  -- The cone is a pure assignment list; nothing writes r1, r2, rst or out.
  have seqSc : SeqBody sc.module.finalize.body := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := invC.typed stq (by
      change stq ∈ sc.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact Or.inl ⟨l, rhs, eq⟩
  have preAssigns : ∀ stq ∈ sc.module.finalize.body, ∃ l rhs, stq = .assign l rhs := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := invC.typed stq (by
      change stq ∈ sc.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact ⟨l, rhs, eq⟩
  have preEq : sc.module.finalize.body = sc.module.body.reverse := by
    simp [Module.finalize]
  have rWNotW : rW ∉ Sparkle.IR.Reorder.writesOf sc.module.finalize.body := by
    intro hwr
    have hf := writes_mem_footprint hwr
    rw [preEq] at hf
    have hfp := (footprint_reverse_mem _ _).mp hf
    have := ordered.2 rW hfp
    rw [freshRWsc] at this; cases this
  have cwNotW : cw ∉ Sparkle.IR.Reorder.writesOf sc.module.finalize.body := by
    intro hwr
    have hf := writes_mem_footprint hwr
    rw [preEq] at hf
    have hfp := (footprint_reverse_mem _ _).mp hf
    have := ordered.2 cw hfp
    rw [freshCw] at this; cases this
  have rstNotW : "rst" ∉ Sparkle.IR.Reorder.writesOf sc.module.finalize.body := by
    intro hwr
    obtain ⟨stq, hst, hz⟩ := List.mem_flatMap.mp hwr
    obtain ⟨l, rhs, eq, htyped⟩ := invC.typed stq (by
      rw [preEq] at hst; exact List.mem_reverse.mp hst)
    subst eq
    simp only [Sparkle.IR.Reorder.stmtWrites, List.mem_singleton] at hz
    subst hz
    have pos := htyped.positive
    rw [widthRst] at pos
    exact Nat.lt_irrefl 0 pos
  have runsC : evalAssigns (declaredWidths st) mems sc.module.finalize.body env0 = some res :=
    invC.runs
  have resRW : res rW = env0 rW := evalAssigns_preserved seqSc runsC rWNotW
  have resCw : res cw = env0 cw := evalAssigns_preserved seqSc runsC cwNotW
  have resRst : res "rst" = env0 "rst" := evalAssigns_preserved seqSc runsC rstNotW
  have cw2Used : sc.usedNames.contains cw2 = true := outcome.used
  have cw2NotOut : cw2 ≠ "out" := by
    intro eq
    have hmem : sm.usedNames.contains cw2 = true := by
      rw [smUsed, mwsO.2.1, siUsed, mwsI.2.1]
      simp [Std.HashSet.contains_insert, cw2Used]
    rw [eq, freshOut] at hmem; cases hmem
  have cwNotOut : cw ≠ "out" := by
    intro eq
    have hmem : sm.usedNames.contains cw = true := by
      rw [smUsed, mwsO.2.1, siUsed, mwsI.2.1, ← hCwm]
      simp [Std.HashSet.contains_insert]
    rw [eq, freshOut] at hmem; cases hmem
  have rWNotOut : rW ≠ "out" := by
    intro eq
    have hmem : sm.usedNames.contains rW = true := by
      rw [smUsed, mwsO.2.1, ← hrWm]
      simp [Std.HashSet.contains_insert]
    rw [eq, freshOut] at hmem; cases hmem
  have wR1 : declaredWidths st rW = w := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    rw [stWires]
    simp [List.find?, Sparkle.IR.Type.HWType.bitWidth]
  have wR2 : declaredWidths st cw = w := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    rw [stWires, siWires]
    have hne' : (rW == cw) = false := by
      cases h : rW == cw
      · rfl
      · exact absurd (by simpa using h) hne
    simp [List.find?, hne', Sparkle.IR.Type.HWType.bitWidth]
  let envF : Env := fun n => if n = "out" then res rW else res n
  have evalFull : evalAssigns (declaredWidths st) mems m.body env0 = some envF := by
    rw [mBody, ← preEq, evalAssigns_append seqSc, runsC]
    show evalAssigns _ mems
      (.register cw "clk" ("rst", .asynchronous) (.ref cw2) v2 ::
        .register rW "clk" ("rst", .asynchronous) (.ref cw) v1 ::
        .assign "out" (.ref rW) :: []) res = _
    simp [evalAssigns, evalExpr, envF]
  have hcw2F : envF cw2 = (eval bvals vvals e).toNat := by
    simp only [envF, if_neg cw2NotOut]
    exact valCw2
  have hcwF : envF cw = env0 cw := by
    simp only [envF, if_neg cwNotOut]
    exact resCw
  have hrstF : envF "rst" = 0 := by
    have : ("rst" : String) ≠ "out" := by decide
    simp only [envF, if_neg this]
    rw [resRst, hrst0]
  have nexts : regNexts (declaredWidths st) mems m.body envF =
      some [(cw, (eval bvals vvals e).toNat), (rW, env0 cw)] := by
    rw [mBody, ← preEq, regNexts_skip_assigns preAssigns]
    show regNexts _ mems
      (.register cw "clk" ("rst", .asynchronous) (.ref cw2) v2 ::
        .register rW "clk" ("rst", .asynchronous) (.ref cw) v1 ::
        .assign "out" (.ref rW) :: []) envF = _
    have maskEq2 : mask (declaredWidths st cw) (eval bvals vvals e).toNat =
        (eval bvals vvals e).toNat := by
      rw [wR2]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    have maskEq1 : mask (declaredWidths st rW) (env0 cw) = env0 cw := by
      rw [wR1]
      exact Nat.mod_eq_of_lt hr2lt
    simp [regNexts, evalExpr, hcw2F, hcwF, hrstF, maskEq2, maskEq1]
  have seqM : SeqBody m.body := by
    rw [mBody, ← preEq]
    intro stq hq
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl (preAssigns stq hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inr ⟨_, _, _, _, _, rfl⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inr ⟨_, _, _, _, _, rfl⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl ⟨_, _, rfl⟩
          · cases hq
  have mem0 : memNexts (declaredWidths st) m.body mems envF = some mems := memNexts_seq seqM
  have scalarSt : ScalarWires st := by
    intro q hq
    rw [stWires] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr ⟨w, rfl⟩
    · rw [siWires] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inr ⟨w, rfl⟩
      · exact frame.scalar (prepare_shape (bs.zip ids) _ (by intro q hq'; rw [show
          (start (entryCompilerState false cache) declName.toString).state =
            CircuitM.init declName.toString from rfl, init_wires] at hq'; cases hq')).1 q hq
  have wm : weOf m = declaredWidths st := by
    rw [weOf_eq_moduleWidths (by
      intro q hq; rw [mWires, List.mem_reverse] at hq; exact scalarSt q hq)]
    exact moduleWidths_finish mWires wiresSt
  -- Sequential zero-width cleanup is the identity on this shape.
  have nodupM : (m.wires.map (·.name)).Nodup := by
    rw [mWires, List.map_reverse]
    exact nodup_reverse wiresSt.1
  have allocM : ∀ q ∈ m.wires, Sparkle.IR.NameHints.Allocated q.name := by
    intro q hq
    rw [mWires, List.mem_reverse] at hq
    exact allocSt q hq
  have outNotWire : "out" ∉ m.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    exact not_allocated_out (eq ▸ allocM q hq)
  have smWires2 : sm.module.wires = { name := rW, ty := .bitVector w } :: si.module.wires := by
    rw [smModule]
    rw [show ∀ (mo : Sparkle.IR.AST.Module) s, (mo.addStmt s).wires = mo.wires from
      fun _ _ => rfl]
    rw [mwsO.2.2.2, ← hrWm]
  have tyEq : ty = .bitVector w := by
    rw [hty]
    unfold Tools.ShippingEntrySoundness.leafOutputType
    rw [smWires2]
    simp [List.find?]
  have mOutputs : m.outputs = [{ name := "out", ty := ty }] := by
    have outputsSm : sm.module.outputs = [] := by
      rw [smModule]
      rw [show ∀ (mo : Sparkle.IR.AST.Module) s, (mo.addStmt s).outputs = mo.outputs from
        fun _ _ => rfl]
      rw [makeWire_outputs, siModule]
      rw [show ∀ (mo : Sparkle.IR.AST.Module) s, (mo.addStmt s).outputs = mo.outputs from
        fun _ _ => rfl]
      rw [makeWire_outputs, frame.outputs,
        (prepare_shape (bs.zip ids) _ (by
          intro q hq'
          rw [show (start (entryCompilerState false cache) declName.toString).state =
            CircuitM.init declName.toString from rfl, init_wires] at hq'
          cases hq')).2]
      rfl
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).outputs = _
    simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
    rw [ht, emitAssign_outputs, addOutput_state]
    simp [Module.addOutput, outputsSm]
  have wmOut : (Sparkle.IR.Optimize.buildWidthMap m).get? "out" = some w := by
    unfold Sparkle.IR.Optimize.buildWidthMap
    rw [Tools.ShippingPostSoundness.wmFold_notin m.wires _ "out" outNotWire, mOutputs]
    simp [Std.HashMap.get?_insert, tyEq, Sparkle.IR.Type.HWType.bitWidth]
  have hwPos : 0 < w := e.wf_pos he
  have bodyEq : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split
    · rfl
    · show m.body.filterMap (Sparkle.IR.ZeroWidth.dzStmt (Sparkle.IR.Optimize.buildWidthMap m))
        = m.body
      apply Tools.ShippingPostSoundness.filterMap_eq_self
      intro stq hst
      rw [mBody] at hst
      rcases List.mem_append.mp hst with hpre | hrest
      · obtain ⟨l, rhs, rfl, htyped⟩ := invC.typed stq (List.mem_reverse.mp hpre)
        have hpos : 0 < weOf m l := by rw [wm]; exact htyped.positive
        have hg := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpos
        have htym : TypedExpr (weOf m) rhs (weOf m l) := by rw [wm]; exact htyped
        have hwmr : ∀ x ∈ Sparkle.IR.Reorder.refsOf rhs,
            Sparkle.IR.ZeroWidth.exprWidth (Sparkle.IR.Optimize.buildWidthMap m) (.ref x) ≠ 0 := by
          intro x hx
          have hpx := htym.refs_positive x hx
          have hgx := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpx
          simp only [Sparkle.IR.ZeroWidth.exprWidth, Std.HashMap.getD_eq_getD_getElem?,
            ← Std.HashMap.get?_eq_getElem?, hgx, Option.getD_some]
          omega
        rw [dzStmt_assign _ _ _ hg (by omega),
          Tools.ShippingTypedPostSoundness.dzExpr_typed htym _ hwmr]
      · rcases List.mem_cons.mp hrest with rfl | hrest
        · simp [Sparkle.IR.ZeroWidth.dzStmt, Sparkle.IR.ZeroWidth.dzExpr]
        · rcases List.mem_cons.mp hrest with rfl | hrest
          · simp [Sparkle.IR.ZeroWidth.dzStmt, Sparkle.IR.ZeroWidth.dzExpr]
          · rcases List.mem_cons.mp hrest with rfl | hnil
            · rw [dzStmt_assign _ _ _ wmOut (by omega)]
              simp [Sparkle.IR.ZeroWidth.dzExpr]
            · cases hnil
  have weEq : weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split
    · rfl
    · exact (weOf_congr_wires rfl).trans (Tools.ShippingPostSoundness.weOf_dropWires m nodupM)
  refine ⟨by rw [wm]; exact wR1, by rw [wm]; exact wR2, bodyEq, weEq, envF, ?_,
    by simp [envF, resRW]⟩
  rw [wm]
  unfold stepModule
  simp [evalFull, nexts, mem0, bind]

theorem synthesizeFromConst_register2_sound {logProf declName ci bs body m d} {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    Register2Preserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_register2_sound run

theorem synthesizeCombinationalCore_register2_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        Register2Preserves declName bs body m := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape =>
    synthesizeFromConst_register2_sound old (shape _) (Tools.ShippingEntrySoundness.entry_kept (shape _) run).mreturns⟩

/-- Position plumbing for the two-stage chain. -/
theorem register2_source {declName : Name} {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr} {m : Sparkle.IR.AST.Module} {dpos : Nat} {w v1 v2 kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (source : Register2Preserves declName bs body m)
    (hbody : body = registerE (inputExpr bs.length dpos) w v1
      (registerE (inputExpr bs.length dpos) w v2
        (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
          (fun j => inputExpr bs.length (vpos j)) e)))
    (hdp : dpos < bs.length)
    (he : e.WF kb kv vw) (hv1 : v1 < 2 ^ w) (hv2 : v2 < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r1 r2 : String), r1 ≠ r2 ∧
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r2 < 2 ^ w →
      weOf m r1 = w ∧ weOf m r2 = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r2, (eval (fun j => bools (bpos j))
            (fun j n => bits (vpos j) n) e).toNat), (r1, env0 r2)], mems) ∧
        envF "out" = env0 r1 := by
  obtain ⟨ids, nd, len, cache, H⟩ := source
  have hQ : instFVars (ids.map Lean.Expr.fvar).toArray 0
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e) =
      quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
        (fun j => .fvar ids[vpos j]!) e := by
    rw [show (Lean.Expr.fvar ids[dpos]!) =
      instFVars (ids.map Lean.Expr.fvar).toArray 0 (inputExpr bs.length dpos) from
      (instantiated_input len hdp).symm]
    apply instantiated_quote _ _ e he
    · intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
    · intro j hj
      obtain ⟨name, pos⟩ := hvp j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
  have qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      registerE (.fvar ids[dpos]!) w v1 (registerE (.fvar ids[dpos]!) w v2
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => .fvar ids[vpos j]!) e)) := by
    rw [hbody, instFVars_registerE, instFVars_registerE, instantiated_input len hdp, hQ]
  obtain ⟨r1, r2, hne, H⟩ := H (.fvar ids[dpos]!) kb kv vw (fun j => ids[bpos j]!)
    (fun j => ids[vpos j]!) e (by rfl) he hv1 hv2 qeq
  refine ⟨ids, nd, len, cache, r1, r2, hne, ?_⟩
  intro bools bits env0 mems values hrst0 hr2lt
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  apply H (boolValues ids bools) (bitValues ids bits) env0 mems
    (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) values _ _ hrst0 hr2lt
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bool_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup
  · intro j hj
    obtain ⟨name, pos⟩ := hvp j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup

/-- General two-stage chain endpoint at the real core entry: each admissible
cycle with reset low and a width-bounded inner state observes the outer
register on `out`, shifts the inner value into the outer register, and steps
the inner register by the source term's value. -/
theorem register2_step_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v1 v2 kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, registerE (inputExpr bs.length dpos) w v1
      (registerE (inputExpr bs.length dpos) w v2
        (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
          (fun j => inputExpr bs.length (vpos j)) e))))
    (hdp : dpos < bs.length)
    (he : e.WF kb kv vw) (hv1 : v1 < 2 ^ w) (hv2 : v2 < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r1 r2 : String), r1 ≠ r2 ∧
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r2 < 2 ^ w →
      weOf m r1 = w ∧ weOf m r2 = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r2, (eval (fun j => bools (bpos j))
            (fun j n => bits (vpos j) n) e).toNat), (r1, env0 r2)], mems) ∧
        envF "out" = env0 r1 := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_register2_sound hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have hdom : ((inputExpr bs.length dpos).isFVar || (inputExpr bs.length dpos).isBVar) = true := by
    simp only [Tools.ShippingMixedSourceBridge.inputExpr]
    rfl
  have mixedGate := register2_term_gate (d := d)
    (by rw [definition]; exact peel) hdom hv1 hv2 he hb hvp
  exact register2_source (source bs _ oldGate mixedGate) rfl hdp he hv1 hv2 hb hvp

/-- Iterating the two-register shift chain along `runModule`: the trace
observes the outer state `S1`, the inner state `S2` follows the cone
(`S2 (j+1) = F (k-1-j)`), and each cycle shifts `S1 (j+1) = S2 j`. The
invariant `P` carries the width bound the outer register's shift needs. -/
theorem trace_of_cycles2 {we : WEnv} {body : List Stmt} {r1 r2 : String} {mems : MEnv}
    {seed : Nat → (String → Nat) → Env} {F : Nat → Nat} {P : Nat → Prop}
    (hne : r1 ≠ r2)
    (step : ∀ t stv, P (stv r2) → ∃ envF,
      stepModule we body (seed t stv) mems =
        some (envF, [(r2, F t), (r1, stv r2)], mems) ∧
      envF "out" = stv r1)
    (Pstep : ∀ t, P (F t)) :
    ∀ (k : Nat) (st0 : String → Nat) (S1 S2 : Nat → Nat), P (st0 r2) →
      S1 0 = st0 r1 → S2 0 = st0 r2 →
      (∀ j, j + 1 ≤ k → S2 (j + 1) = F (k - 1 - j)) →
      (∀ j, j + 1 ≤ k → S1 (j + 1) = S2 j) →
      ∃ envs, runModule we body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S1 j
  | 0, st0, S1, S2, _, hS10, hS20, hS2s, hS1s =>
    ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, st0, S1, S2, P0, hS10, hS20, hS2s, hS1s => by
    obtain ⟨envF, hstep, hout⟩ := step k st0 P0
    have hnext2 : applyNexts st0 [(r2, F k), (r1, st0 r2)] r2 = F k := by
      simp [applyNexts]
    have hnext1 : applyNexts st0 [(r2, F k), (r1, st0 r2)] r1 = st0 r2 := by
      have hne' : (r2 == r1) = false := by
        cases h : r2 == r1
        · rfl
        · exact absurd (eq_of_beq h).symm hne
      simp [applyNexts, hne']
    obtain ⟨rest, hrun, hlen, hobs⟩ := trace_of_cycles2 hne step Pstep k
      (applyNexts st0 [(r2, F k), (r1, st0 r2)]) (fun j => S1 (j + 1)) (fun j => S2 (j + 1))
      (by rw [hnext2]; exact Pstep k)
      (by
        show S1 (0 + 1) = _
        rw [hnext1, hS1s 0 (by omega), hS20])
      (by
        show S2 (0 + 1) = _
        rw [hnext2, hS2s 0 (by omega)]
        simp)
      (by
        intro j hj
        show S2 (j + 1 + 1) = F (k - 1 - j)
        rw [hS2s (j + 1) (by omega)]
        have hidx : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
        rw [hidx])
      (by
        intro j hj
        show S1 (j + 1 + 1) = S2 (j + 1)
        exact hS1s (j + 1) (by omega))
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj
      cases j with
      | zero => rw [hS10]; simpa using hout
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget]
        exact hobs i hi

/-- Packaged two-stage chain trace at the real core entry: the compiled
`runModule` trace observes the outer register's stream, one cycle behind the
inner register, which follows the source cone. -/
theorem register2_run_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {dpos : Nat} {w v1 v2 kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, registerE (inputExpr bs.length dpos) w v1
      (registerE (inputExpr bs.length dpos) w v2
        (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j))
          (fun j => inputExpr bs.length (vpos j)) e))))
    (hdp : dpos < bs.length)
    (he : e.WF kb kv vw) (hv1 : v1 < 2 ^ w) (hv2 : v2 < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r1 r2 : String), r1 ≠ r2 ∧
      ∀ (bools : Nat → Nat → Bool) (bits : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat) (S1 S2 : Nat → Nat),
      (∀ t stv, SourceInputs declName bs ids cache (bools (k - 1 - t)) (bits (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧
          seed t stv r1 = stv r1 ∧ seed t stv r2 = stv r2) →
      st0 r2 < 2 ^ w →
      S1 0 = st0 r1 → S2 0 = st0 r2 →
      (∀ j, j + 1 ≤ k → S2 (j + 1) = (eval (fun i => bools j (bpos i))
        (fun i n => bits j (vpos i) n) e).toNat) →
      (∀ j, j + 1 ≤ k → S1 (j + 1) = S2 j) →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S1 j := by
  obtain ⟨ids, nd, len, cache, r1, r2, hne, H⟩ :=
    register2_step_of_env hr env old peel hdp he hv1 hv2 hb hvp
  refine ⟨ids, nd, len, cache, r1, r2, hne, ?_⟩
  intro bools bits mems k seed st0 S1 S2 hseed hst0 hS10 hS20 hS2s hS1s
  apply trace_of_cycles2 (P := fun s => s < 2 ^ w) hne
    (F := fun t => (eval (fun i => bools (k - 1 - t) (bpos i))
      (fun i n => bits (k - 1 - t) (vpos i) n) e).toNat)
    ?_ ?_ k st0 S1 S2 hst0 hS10 hS20 ?_ hS1s
  · intro t stv hP
    obtain ⟨hsrc, hrst, hread1, hread2⟩ := hseed t stv
    obtain ⟨-, -, -, -, envF, hstep, hout⟩ :=
      H (bools (k - 1 - t)) (bits (k - 1 - t)) (seed t stv) mems hsrc hrst
        (by rw [hread2]; exact hP)
    refine ⟨envF, ?_, by rw [hout, hread1]⟩
    rw [hread2] at hstep
    exact hstep
  · intro t
    exact BitVec.isLt _
  · intro j hj
    rw [hS2s j hj]
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    rw [hidx]

/-- The reduced single-slot `circuit do` state: `runCircuitH` with one
register slot builds `Signal.loop` over `bundle2 (register …) (pure ())` and
observes it through `Signal.map Prod.fst`. That observation is exactly the
plain feedback-register stream (the anchor for the planned `circuit do`
reification onto the certified loop shape). -/
theorem map_fst_loop_register {D : Sparkle.Core.Domain.DomainConfig} {w : Nat}
    (init : BitVec w)
    (cone : Sparkle.Core.Signal.Signal D (BitVec w) →
      Sparkle.Core.Signal.Signal D (BitVec w))
    (hcone : ∀ (s₁ s₂ : Sparkle.Core.Signal.Signal D (BitVec w)) (t : Nat),
      s₁.val t = s₂.val t → (cone s₁).val t = (cone s₂).val t) :
    ∀ t, (Sparkle.Core.Signal.Signal.map Prod.fst (Sparkle.Core.Signal.Signal.loop
        (fun live => Sparkle.Core.Signal.bundle2
          (Sparkle.Core.Signal.Signal.register init
            (cone (Sparkle.Core.Signal.Signal.map Prod.fst live)))
          (Sparkle.Core.Signal.Signal.pure ())))).val t =
      (Sparkle.Core.Signal.Signal.loop
        (fun s => Sparkle.Core.Signal.Signal.register init (cone s))).val t := by
  have hR := loop_register_val init cone hcone
  intro t
  induction t with
  | zero =>
    show Prod.fst (Sparkle.Core.Signal.Signal.loopGo _ 0) = _
    rw [Sparkle.Core.Signal.Signal.loopGo_eq, hR.1]
    rfl
  | succ t ih =>
    show Prod.fst (Sparkle.Core.Signal.Signal.loopGo _ (t + 1)) = _
    rw [Sparkle.Core.Signal.Signal.loopGo_eq, hR.2 t]
    show (cone (Sparkle.Core.Signal.Signal.map Prod.fst
      ⟨fun i => if i < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ i else default⟩)).val t = _
    apply hcone
    show Prod.fst (if t < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ t else default) = _
    rw [if_pos (by omega)]
    exact ih

/-! ## The single-slot `circuit do` root -/

/-- `Type`-level list/HList scaffolding of the one-slot `runCircuitH` call. -/
def sort1E : Lean.Expr := .sort (.succ .zero)
def nilTE : Lean.Expr := .app (.const ``List.nil [.succ .zero]) sort1E
def consTE (w : Nat) : Lean.Expr :=
  mkApp3 (.const ``List.cons [.succ .zero]) sort1E (bitVecE w) nilTE
def hlE (w : Nat) : Lean.Expr := .app (.const ``Sparkle.Core.HList []) (consTE w)
def hlNilE : Lean.Expr := .app (.const ``Sparkle.Core.HList []) nilTE
def sigLE (dom : Lean.Expr) (w : Nat) : Lean.Expr :=
  mkApp2 (.const ``Sparkle.Core.Circuit.SigList []) dom (consTE w)
def regTE (dom : Lean.Expr) (w : Nat) : Lean.Expr :=
  mkApp4 (.const ``Sparkle.Core.Reg []) dom (hlE w) (sigLE dom w) (bitVecE w)
def slotTE (dom : Lean.Expr) (w : Nat) : Lean.Expr :=
  mkApp4 (.const ``Sparkle.Core.Circuit.Slot []) dom (hlE w) (sigLE dom w) (bitVecE w)

/-- The coerced live read of the register handle. -/
def readE (dom : Lean.Expr) (w : Nat) (x : Lean.Expr) : Lean.Expr :=
  mkApp3 (.const ``Prod.fst [.zero, .zero]) (sigT dom w) (slotTE dom w) x

/-- The one-slot `circuit do` exactly as the macro elaborates it over a
polymorphic domain (`dom0`–`dom3` are the domain at the successive binder
depths; the cone `rhs` sits under the handle-tuple binder and the projected
handle `let`). -/
def cdoE (nmR : Name) (dom0 dom1 dom2 dom3 : Lean.Expr) (w v : Nat) (rhs : Lean.Expr) : Lean.Expr :=
  mkApp8 (.const ``Sparkle.Core.runCircuitH []) dom0 (consTE w) (sigT dom0 w)
    (mkApp2 (.const ``Sparkle.Core.instHasDomainSignal []) dom0 (bitVecE w))
    (mkApp4 (.const ``Sparkle.Core.instHListWireableConsOfWireable []) (bitVecE w) nilTE
      (.app (.const ``Sparkle.Core.instWireableBitVec []) (natE w))
      (.const ``Sparkle.Core.instHListWireableNil []))
    (mkApp4 (.const ``instInhabitedProd [.zero, .zero]) (bitVecE w) hlNilE
      (.app (.const ``BitVec.instInhabited []) (natE w))
      (.const ``instInhabitedPUnit [.succ .zero]))
    (mkApp4 (.const ``Prod.mk [.zero, .zero]) (bitVecE w) hlNilE
      (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v)) (.const ``Unit.unit []))
    (.lam `_cdoRegs (mkApp4 (.const ``Sparkle.Core.RegList []) dom0 (hlE w) (sigLE dom0 w) (consTE w))
      (.letE nmR (regTE dom1 w)
        (mkApp3 (.const ``Prod.fst [.zero, .zero]) (regTE dom1 w)
          (mkApp4 (.const ``Sparkle.Core.RegList []) dom1 (hlE w) (sigLE dom1 w) nilTE)
          (.bvar 0))
        (mkApp6 (.const ``Sparkle.Core.Circuit.bind []) dom2 (sigLE dom2 w) (.const ``Unit [])
          (sigT dom2 w)
          (mkApp6 (.const ``Sparkle.Core.Circuit.next []) dom2 (hlE w) (bitVecE w)
            (sigLE dom2 w) (.bvar 0) rhs)
          (.lam `_cdoK (.const ``Unit [])
            (mkApp4 (.const ``Sparkle.Core.Circuit.pure' []) dom3 (sigLE dom3 w)
              (sigT dom3 w) (readE dom3 w (.bvar 1)))
            .default))
        true)
      .default)

theorem cdoConeToLoop_readE_self (dom : Lean.Expr) (w : Nat) :
    cdoConeToLoop 0 (readE dom w (.bvar 0)) = some (.bvar 0) := rfl

theorem cdoConeToLoop_input {n i : Nat} (h : i < n) :
    cdoConeToLoop 0 (inputExpr (n + 2) i) = some (inputExpr (n + 1) i) := by
  show cdoConeToLoop 0 (.bvar (n + 2 - 1 - i)) = some (.bvar (n + 1 - 1 - i))
  have hor : (n + 2 - 1 - i == 0 || n + 2 - 1 - i == 0 + 1) = false := by
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    omega
  have h2 : n + 2 - 1 - i > 0 + 1 := by omega
  have key : n + 2 - 1 - i - 1 = n + 1 - 1 - i := by omega
  simp only [cdoConeToLoop, hor, Bool.false_eq_true, if_false, if_pos h2, key]

theorem cdoConeToLoop_natE (d n : Nat) : cdoConeToLoop d (natE n) = some (natE n) := rfl

theorem cdoConeToLoop_bitVecE (d n : Nat) :
    cdoConeToLoop d (bitVecE n) = some (bitVecE n) := rfl

theorem cdoConeToLoop_sigT {domS domL : Lean.Expr}
    (h : cdoConeToLoop 0 domS = some domL) (w : Nat) :
    cdoConeToLoop 0 (sigT domS w) = some (sigT domL w) := by
  simp [sigT, cdoConeToLoop, h, cdoConeToLoop_natE, mkApp2, mkAppB, mkApp]

/-- `cdoConeToLoop` distributes over the unified quote: recognized leaves map
by the given facts and every node skeleton just shifts its embedded domain. -/
theorem cdoConeToLoop_quote {domS domL : Lean.Expr} {bi vi biL viL : Nat → Lean.Expr}
    {kb kv : Nat} {vw : Nat → Nat}
    (hdom : cdoConeToLoop 0 domS = some domL)
    (hb : ∀ j, j < kb → cdoConeToLoop 0 (bi j) = some (biL j))
    (hv : ∀ j, j < kv → cdoConeToLoop 0 (vi j) = some (viL j)) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw →
    cdoConeToLoop 0 (quote domS bi vi e) = some (quote domL biL viL e)
  | _, .boolInput j, he => hb j he
  | _, .bitsInput _ j, he => hv j he.1
  | _, .boolLit b, _ => by
    cases b <;> simp [Tools.ShippingUnifiedSource.quote, literalE, boolName, cdoConeToLoop, cdoConeToLoop_natE, cdoConeToLoop_bitVecE, cdoConeToLoop_sigT hdom, hdom, sigT, binMethod, binInst, compareName, signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp]
  | _, .bitsLit w v, _ => by
    simp [Tools.ShippingUnifiedSource.quote, quoteF, cdoConeToLoop, cdoConeToLoop_natE, cdoConeToLoop_bitVecE, cdoConeToLoop_sigT hdom, hdom, sigT, binMethod, binInst, compareName, signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp]
  | _, .binary op a b, he => by
    have ia := cdoConeToLoop_quote hdom hb hv a he.1
    have ib := cdoConeToLoop_quote hdom hb hv b he.2
    cases op <;> simp [Tools.ShippingUnifiedSource.quote, binE, cdoConeToLoop, cdoConeToLoop_natE, cdoConeToLoop_bitVecE, cdoConeToLoop_sigT hdom, hdom, sigT, binMethod, binInst, compareName, signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia, ib]
  | _, .compare op a b, he => by
    have ia := cdoConeToLoop_quote hdom hb hv a he.1
    have ib := cdoConeToLoop_quote hdom hb hv b he.2
    cases op <;> simp [Tools.ShippingUnifiedSource.quote, compareE, cdoConeToLoop, cdoConeToLoop_natE, cdoConeToLoop_bitVecE, cdoConeToLoop_sigT hdom, hdom, sigT, binMethod, binInst, compareName, signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia, ib]
  | _, .boolBinary op a b, he => by
    have ia := cdoConeToLoop_quote hdom hb hv a he.1
    have ib := cdoConeToLoop_quote hdom hb hv b he.2
    cases op <;> simp [Tools.ShippingUnifiedSource.quote, boolBinE, cdoConeToLoop, cdoConeToLoop_natE, cdoConeToLoop_bitVecE, cdoConeToLoop_sigT hdom, hdom, sigT, binMethod, binInst, compareName, signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia, ib]
  | _, .boolNot a, he => by
    have ia := cdoConeToLoop_quote hdom hb hv a he
    simp [Tools.ShippingUnifiedSource.quote, boolNotE, cdoConeToLoop, cdoConeToLoop_natE, cdoConeToLoop_bitVecE, cdoConeToLoop_sigT hdom, hdom, sigT, binMethod, binInst, compareName, signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia]
  | _, .boolEq a b, he => by
    have ia := cdoConeToLoop_quote hdom hb hv a he.1
    have ib := cdoConeToLoop_quote hdom hb hv b he.2
    simp [Tools.ShippingUnifiedSource.quote, boolEqE, cdoConeToLoop, cdoConeToLoop_natE, cdoConeToLoop_bitVecE, cdoConeToLoop_sigT hdom, hdom, sigT, binMethod, binInst, compareName, signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia, ib]
  | s, .mux c a b, he => by
    have ic := cdoConeToLoop_quote hdom hb hv c he.1
    have ia := cdoConeToLoop_quote hdom hb hv a he.2.1
    have ib := cdoConeToLoop_quote hdom hb hv b he.2.2
    cases s <;> simp [Tools.ShippingUnifiedSource.quote, muxE, SType.quoteType, cdoConeToLoop, cdoConeToLoop_natE, cdoConeToLoop_bitVecE, cdoConeToLoop_sigT hdom, hdom, sigT, binMethod, binInst, compareName, signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ic, ia, ib]
  | _, .setw w' a, he => by
    have ia := cdoConeToLoop_quote hdom hb hv a he.1
    simp [Tools.ShippingUnifiedSource.quote, setwE, cdoConeToLoop, cdoConeToLoop_natE, cdoConeToLoop_bitVecE, cdoConeToLoop_sigT hdom, hdom, sigT, binMethod, binInst, compareName, signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia]

theorem canonicalCircuitDo?_cdoE {nmR : Name} {dom0 dom1 dom2 dom3 rhs cone : Lean.Expr} {w v : Nat}
    (hdom : (dom0.isFVar || dom0.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (hcone : cdoConeToLoop 0 rhs = some cone) :
    canonicalCircuitDo? (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = some (w, v, cone) := by
  have hlit := litValue_natE w v hv
  simp only [mkApp2, mkAppB, mkApp] at hlit
  simp only [cdoE, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp,
    readE, regTE, slotTE, sigLE, hlE, consTE, nilTE, hlNilE, sort1E, sigT, bitVecE,
    canonicalCircuitDo?, hdom, if_true, canonicalNatLitValue?_natE, hlit, hcone]
  simp [hw]

theorem instFVars_cdoE (xs : Array Lean.Expr) (d : Nat) (nmR : Name) (dom0 dom1 dom2 dom3 : Lean.Expr)
    (w v : Nat) (rhs : Lean.Expr) :
    instFVars xs d (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) =
      cdoE nmR (instFVars xs d dom0) (instFVars xs (d + 1) dom1) (instFVars xs (d + 2) dom2)
        (instFVars xs (d + 3) dom3) w v (instFVars xs (d + 2) rhs) := rfl

set_option maxHeartbeats 1000000 in
theorem cdoUncached_cdoE (rec : TranslateFn) {nmR : Name} {dom0 dom1 dom2 dom3 rhs cone : Lean.Expr}
    {w v : Nat}
    (hdom : (dom0.isFVar || dom0.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (hcone : cdoConeToLoop 0 rhs = some cone) (hint : String) (top named : Bool) :
    translateCircuitDoUncachedWith rec w v (cdoE nmR dom0 dom1 dom2 dom3 w v rhs)
        hint top named =
      (do
        let selfId ← CompilerM.liftMetaM Lean.mkFreshFVarId
        if (← CompilerM.lookupVar selfId).isSome then
          throw (Exception.error .missing "circuit-do binder id collision")
        let r ← CompilerM.makeWire hint (.bitVector w) (named := named)
        CompilerM.bindSourceVariable selfId r
        let cw ← rec (instFVars #[.fvar selfId] 0 cone) "loop_body" false false
        CompilerM.emitRegisterStmt r "clk" "rst" (.ref cw) v
        return r) := by
  unfold translateCircuitDoUncachedWith
  rw [canonicalCircuitDo?_cdoE hdom hw hv hcone]

set_option maxHeartbeats 1000000 in
theorem cdo_step (rec : TranslateFn) {nmR : Name} {dom0 dom1 dom2 dom3 rhs cone : Lean.Expr} {w v : Nat}
    (hdom : (dom0.isFVar || dom0.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (hcone : cdoConeToLoop 0 rhs = some cone) (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (cdoE nmR dom0 dom1 dom2 dom3 w v rhs)
        hint top named =
      translateControlCachedWith (translateCircuitDoUncachedWith rec w v)
        (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) hint top named := by
  have shape : translateCoreShape (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = false := rfl
  have core : translateCore rec (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) hint top named =
    pure none := rfl
  have control : isBoolControl (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = false := rfl
  have mux : canonicalMuxType? (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = none := rfl
  have setw : canonicalSetWidth? (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = none := rfl
  have reg : canonicalRegister? (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = none := rfl
  have regEn : canonicalRegisterEnable? (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = none := rfl
  have loopReg : canonicalLoopRegister? (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = none := rfl
  have cdo := canonicalCircuitDo?_cdoE (nmR := nmR) (dom1 := dom1) (dom2 := dom2)
    (dom3 := dom3) hdom hw hv hcone
  have step : translateStepWith translateFallback rec (cdoE nmR dom0 dom1 dom2 dom3 w v rhs)
      hint top named =
      translateFallback rec (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, control, Bool.false_eq_true, if_false, mux, setw, reg,
    regEn, loopReg, cdo]

theorem unifiedRegisterRoot_cdoE {kinds : Array MixedGateBinder}
    {nmR : Name} {dom0 dom1 dom2 dom3 rhs cone : Lean.Expr} {w v : Nat}
    (hdom : (dom0.isFVar || dom0.isBVar) = true) (hw : 0 < w) (hv : v < 2 ^ w)
    (hcone : cdoConeToLoop 0 rhs = some cone)
    (body : unifiedGateBitsBody (kinds.push (.bits w)) w cone = true) :
    unifiedRegisterRoot kinds (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = true := by
  unfold unifiedRegisterRoot
  have hreg : canonicalRegister? (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = none := rfl
  have hregEn : canonicalRegisterEnable? (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = none := rfl
  have hloop : canonicalLoopRegister? (cdoE nmR dom0 dom1 dom2 dom3 w v rhs) = none := rfl
  rw [hreg, hregEn, hloop, canonicalCircuitDo?_cdoE hdom hw hv hcone]
  simp [hw, body]

theorem cdoConeToLoop_fvar (d : Nat) (id : FVarId) :
    cdoConeToLoop d (.fvar id) = some (.fvar id) := rfl

/-- The canonical read-quoted circuit-do cone normalizes to the loop-form
quote, at loose-bvar inputs (gate time). -/
theorem cdoConeToLoop_quote_inputs {n dpos kb kv : Nat} {vw : Nat → Nat} {w : Nat}
    {bpos vpos : Nat → Nat}
    (hdp : dpos < n)
    (hb : ∀ j, j < kb → bpos j < n)
    (hvp : ∀ j, j < kv → vpos j < n)
    (e : Term (.bits w)) (he : e.WF kb (kv + 1) vw) :
    cdoConeToLoop 0 (quote (inputExpr (n + 2) dpos)
      (fun j => inputExpr (n + 2) (bpos j))
      (fun j => if j = kv then readE (inputExpr (n + 2) dpos) w (.bvar 0)
        else inputExpr (n + 2) (vpos j)) e) =
    some (quote (inputExpr (n + 1) dpos)
      (fun j => inputExpr (n + 1) (bpos j))
      (fun j => if j = kv then .bvar 0 else inputExpr (n + 1) (vpos j)) e) := by
  apply cdoConeToLoop_quote (cdoConeToLoop_input hdp)
    (fun j hj => cdoConeToLoop_input (hb j hj)) _ e he
  intro j hj
  by_cases hkv : j = kv
  · subst hkv
    simp only [if_pos rfl]
    exact cdoConeToLoop_readE_self _ _
  · have hjlt : j < kv := by omega
    simp only [if_neg hkv]
    exact cdoConeToLoop_input (hvp j hjlt)

/-- Gate acceptance for the peeled circuit-do declaration. -/
theorem cdo_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {nmR : Name} {dpos : Nat} {w v : Nat} {kb kv : Nat} {vw : Nat → Nat}
    {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (peel : mixedGatePeel d.value = some (bs, cdoE nmR (inputExpr bs.length dpos)
      (inputExpr (bs.length + 1) dpos) (inputExpr (bs.length + 2) dpos)
      (inputExpr (bs.length + 3) dpos) w v
      (quote (inputExpr (bs.length + 2) dpos)
        (fun j => inputExpr (bs.length + 2) (bpos j))
        (fun j => if j = kv then readE (inputExpr (bs.length + 2) dpos) w (.bvar 0)
          else inputExpr (bs.length + 2) (vpos j)) e)))
    (hdp : dpos < bs.length) (hself : vw kv = w) (hv : v < 2 ^ w)
    (he : e.WF kb (kv + 1) vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∀ isInst, mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, cdoE nmR (inputExpr bs.length dpos)
      (inputExpr (bs.length + 1) dpos) (inputExpr (bs.length + 2) dpos)
      (inputExpr (bs.length + 3) dpos) w v
      (quote (inputExpr (bs.length + 2) dpos)
        (fun j => inputExpr (bs.length + 2) (bpos j))
        (fun j => if j = kv then readE (inputExpr (bs.length + 2) dpos) w (.bvar 0)
          else inputExpr (bs.length + 2) (vpos j)) e)) := by
  intro isInst
  have hcone := cdoConeToLoop_quote_inputs hdp
    (fun j hj => (hb j hj).elim fun name pos =>
      Nat.lt_of_lt_of_le (List.getElem_of_getElem? pos).choose (Nat.le_refl _))
    (fun j hj => (hvp j hj).elim fun name pos =>
      Nat.lt_of_lt_of_le (List.getElem_of_getElem? pos).choose (Nat.le_refl _))
    e he
  have body : unifiedGateBitsBody ((bs.map Prod.snd).toArray.push (.bits w)) w
      (quote (inputExpr (bs.length + 1) dpos)
        (fun j => inputExpr (bs.length + 1) (bpos j))
        (fun j => if j = kv then .bvar 0 else inputExpr (bs.length + 1) (vpos j)) e) = true :=
    unified_quote_accepted
      (fun j hj => (hb j hj).elim fun name pos => input_bool_accepted_push pos)
      (fun j hj => by
        by_cases hkv : j = kv
        · subst hkv
          simp only [if_pos rfl]
          rw [hself]
          exact self_bits_accepted
        · have hjlt : j < kv := by omega
          simp only [if_neg hkv]
          exact (hvp j hjlt).elim fun name pos => input_bits_accepted_push pos)
      e he
  have hdom : ((inputExpr bs.length dpos).isFVar || (inputExpr bs.length dpos).isBVar)
      = true := by
    simp only [Tools.ShippingMixedSourceBridge.inputExpr]
    rfl
  have root := unifiedRegisterRoot_cdoE (nmR := nmR)
    (dom1 := inputExpr (bs.length + 1) dpos)
    (dom2 := inputExpr (bs.length + 2) dpos) (dom3 := inputExpr (bs.length + 3) dpos)
    hdom (e.wf_pos he) hv hcone body
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, Bool.or_true, Bool.true_or, if_true]

def CdoPreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (nmR : Name) (dom dom1 dom2 dom3 : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (binp vinp : Nat → FVarId)
      {w v : Nat} (e : Term (.bits w)),
    (dom.isFVar || dom.isBVar) = true → cdoConeToLoop 0 dom2 = some dom2 →
    vw kv = w → e.WF kb (kv + 1) vw → v < 2 ^ w →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      cdoE nmR dom dom1 dom2 dom3 w v
        (quote dom2 (fun j => .fvar (binp j))
          (fun j => if j = kv then readE dom2 w (.bvar 0) else .fvar (vinp j)) e) →
    ∃ r : String,
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (mems : MEnv)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (n : Nat) → BitVec n),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨vw j, vvals j (vw j)⟩) →
    env0 "rst" = 0 → env0 r < 2 ^ w →
    weOf m r = w ∧
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
    weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
    ∃ envF, stepModule (weOf m) m.body env0 mems =
        some (envF, [(r, (eval bvals
          (fun j n => if j = kv then BitVec.ofNat n (env0 r) else vvals j n) e).toNat)],
          mems) ∧
      envF "out" = env0 r

set_option maxHeartbeats 1000000 in
theorem synthesizeMixedCertified_cdo_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    CdoPreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, _⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro nmR dom dom1 dom2 dom3 kb kv vw binp vinp w v e hdom hdom2 hself he hv qeq
  have hconeF : cdoConeToLoop 0
      (quote dom2 (fun j => .fvar (binp j))
        (fun j => if j = kv then readE dom2 w (.bvar 0) else .fvar (vinp j)) e) =
      some (quote dom2 (fun j => .fvar (binp j))
        (fun j => if j = kv then .bvar 0 else .fvar (vinp j)) e) := by
    apply cdoConeToLoop_quote hdom2 (fun j _ => cdoConeToLoop_fvar 0 (binp j)) _ e he
    intro j hj
    by_cases hkv : j = kv
    · subst hkv
      simp only [if_pos rfl]
      exact cdoConeToLoop_readE_self _ _
    · simp only [if_neg hkv]
      exact cdoConeToLoop_fvar 0 (vinp j)
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) (bools := fun _ => false)
    (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨rW, sm, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have hw : 0 < w := by
    have := e.wf_pos he
    exact this
  have stepEq : translateExprToWire (cdoE nmR dom dom1 dom2 dom3 w v
        (quote dom2 (fun j => .fvar (binp j))
          (fun j => if j = kv then readE dom2 w (.bvar 0) else .fvar (vinp j)) e)) "out" false true =
      translateControlCachedWith (translateCircuitDoUncachedWith
          (translateFuelFix translateStep 1048575) w v)
        (cdoE nmR dom dom1 dom2 dom3 w v
          (quote dom2 (fun j => .fvar (binp j))
            (fun j => if j = kv then readE dom2 w (.bvar 0) else .fvar (vinp j)) e)) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (cdoE nmR dom dom1 dom2 dom3 w v
        (quote dom2 (fun j => .fvar (binp j))
          (fun j => if j = kv then readE dom2 w (.bvar 0) else .fvar (vinp j)) e)) "out" false true = _
    rw [cdo_step _ hdom hw hv hconeF]
  rw [stepEq] at tr
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec rW rfl
    rw [record0] at dead
    simp at dead
  rw [cdoUncached_cdoE _ hdom hw hv hconeF] at missRun
  obtain ⟨selfId, sf, rfresh, missRun⟩ := Returns.bind missRun
  have hsf : sf = _ := Returns.liftMetaM rfresh
  subst hsf
  obtain ⟨aOpt, sg, rlook, missRun⟩ := Returns.bind missRun
  obtain ⟨hsg, hvisEq⟩ := lookupVar_returns rlook
  subst hsg
  cases hopt : aOpt.isSome with
  | true =>
    rw [hopt] at missRun
    simp only [if_true] at missRun
    obtain ⟨_, _, hthrow, _⟩ := Returns.bind missRun
    exact (Returns.throw hthrow).elim
  | false =>
    rw [hopt] at missRun
    simp only [Bool.false_eq_true, if_false] at missRun
    have hvis : Tools.ShippingBindingsSoundness.visible
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings
        selfId = none := by
      rw [← hvisEq]
      exact Option.not_isSome_iff_eq_none.mp (by simp [hopt])
    have missRun2 : Returns (do
        let r ← CompilerM.makeWire "out" (.bitVector w) (named := true)
        CompilerM.bindSourceVariable selfId r
        let cw ← translateFuelFix translateStep 1048575
          (instFVars #[.fvar selfId] 0
            (quote dom2 (fun j => .fvar (binp j))
              (fun j => if j = kv then .bvar 0 else .fvar (vinp j)) e))
          "loop_body" false false
        CompilerM.emitRegisterStmt r "clk" "rst" (.ref cw) v
        pure r)
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state rW smR := missRun
    obtain ⟨r0, s1, rmk, missRun3⟩ := Returns.bind missRun2
    obtain ⟨hr0, hs1⟩ := makeWire_returns rmk
    obtain ⟨ub, s2, rbind, missRun4⟩ := Returns.bind missRun3
    have hs2 := bindSourceVariable_returns rbind
    obtain ⟨cw, sc, rc, missRun5⟩ := Returns.bind missRun4
    obtain ⟨ue, s4, remit, rpure⟩ := Returns.bind missRun5
    have hs4 := emitRegisterStmt_returns remit
    obtain ⟨hrWeq, hsmR⟩ := Returns.pure rpure
    subst hrWeq
    have hrec := recordTranslation_returns record
    -- Static shapes.
    have stBody : st.module.body =
        .assign "out" (.ref rW) ::
          .register rW "clk" ("rst", .asynchronous) (.ref cw) v :: sc.module.body := by
      rw [ht, emitAssign_body_cons, addOutput_state]
      show _ :: (sm.module.addOutput _).body = _
      rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).body = mo.body from
        fun _ _ => rfl, hrec]
      show _ :: smR.module.body = _
      rw [hsmR, hs4]
      rfl
    have stWires : st.module.wires = sc.module.wires := by
      rw [ht, emitAssign_wires, addOutput_state]
      show (sm.module.addOutput _).wires = _
      rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).wires = mo.wires from
        fun _ _ => rfl, hrec]
      show smR.module.wires = _
      rw [hsmR, hs4]
      rfl
    have stUsed : st.usedNames = sc.usedNames.insert "out" := by
      rw [ht, emitAssign_usedNames, addOutput_state]
      show sm.usedNames.insert "out" = _
      rw [hrec]
      show smR.usedNames.insert "out" = _
      rw [hsmR, hs4]
    have mBody : m.body = sc.module.body.reverse ++
        [.register rW "clk" ("rst", .asynchronous) (.ref cw) v, .assign "out" (.ref rW)] := by
      rw [hm]
      show ((addClockResetIfSequential st.module).finalize).body = _
      simp only [Module.finalize, (addClockReset_facts st.module).1, stBody]
      simp
    have mWires : m.wires = st.module.wires.reverse := by
      rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
    refine ⟨rW, ?_⟩
    intro bools bits env0 mems bvals vvals a p adm hb0 hv0 hrst0 hstb
    have empty := empty_layout (entryCompilerState false cache) declName.toString env0
    have prepared := prepare_layout (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
    obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
      (bs.zip ids) _ _ rfl rfl
    rw [pc] at rc
    rw [ps] at hs1 hr0
    rw [pc, ps] at hvis
    have mws := CircuitM.makeWire_spec "out" (.bitVector w) true
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state
    have freshR : (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.usedNames.contains rW
        = false := by rw [hr0]; exact mws.1
    -- The fresh binder differs from every prepared input binder.
    have hvisVar : (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup selfId
        = none := by
      revert hvis
      unfold Tools.ShippingBindingsSoundness.visible
      cases (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup selfId
      · intro _; rfl
      · intro hcon; cases hcon
    have hvisPer : (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.get?
        selfId.name = none := by
      revert hvis
      unfold Tools.ShippingBindingsSoundness.visible
      rw [hvisVar]
      intro h; exact h
    have selfNe : ∀ id, Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings id ≠
        none → id ≠ selfId := by
      intro id hne heq
      subst heq
      exact hne hvis
    -- Bindings and visibility at the child entry state.
    have s2Bind : s2.sourceBindings = (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.insert
        selfId.name rW := by
      rw [hs2]
      show s1.sourceBindings.insert selfId.name rW = _
      rw [hs1, CircuitM.makeWire_sourceBindings]
    have s2Used : s2.usedNames = (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.usedNames.insert rW := by
      rw [hs2]
      show s1.usedNames = _
      rw [hs1, mws.2.1, hr0]
    have s2Module : s2.module = (CircuitM.makeWire "out" (.bitVector w) true
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state).2.module := by
      rw [hs2]
      show s1.module = _
      rw [hs1]
    have visSelf : Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        s2.sourceBindings selfId = some rW := by
      unfold Tools.ShippingBindingsSoundness.visible
      rw [hvisVar, s2Bind]
      simp [Std.HashMap.get?_insert]
    have visOld : ∀ id z, id ≠ selfId →
        Tools.ShippingBindingsSoundness.visible
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).context
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).state.sourceBindings id
          = some z →
        Tools.ShippingBindingsSoundness.visible
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).context
          s2.sourceBindings id = some z := by
      intro id z hne hz
      unfold Tools.ShippingBindingsSoundness.visible at hz ⊢
      rw [s2Bind]
      cases hvm : (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup id with
      | some u => rw [hvm] at hz; exact hz
      | none =>
        rw [hvm] at hz
        have hz' : (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.get?
            id.name = some z := hz
        have hname : ¬ (id.name == selfId.name) = true := by
          simp only [beq_iff_eq]
          intro h
          exact hne (fvarId_name_inj h)
        show ((prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.insert
            selfId.name rW).get? id.name = some z
        have hname' : ¬ (selfId.name = id.name) := fun h => hne (fvarId_name_inj h.symm)
        simpa [Std.HashMap.getElem?_insert, hname'] using hz'
    -- Extended per-cycle valuation: the loop binder is input `kv` at wire rW.
    have selfNeB : ∀ j, j < kb → binp j ≠ selfId := by
      intro j hj
      obtain ⟨wj, hbnd, -⟩ := prepared.1.bool (binp j) (bvals j) (hb0 j hj)
      exact selfNe _ (by rw [hbnd]; simp)
    have selfNeV : ∀ j, j < kv → vinp j ≠ selfId := by
      intro j hj
      obtain ⟨wj, hbnd, -⟩ := prepared.1.bits (vinp j) (vw j) (vvals j (vw j)) (hv0 j hj)
      exact selfNe _ (by rw [hbnd]; simp)
    have hb' : ∀ j, j < kb →
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id) (binp j) =
        some (.bool (bvals j)) := by
      intro j hj
      simp only [if_neg (selfNeB j hj)]
      exact inputValues_bool (hb0 j hj)
    have separate := prepared.1.separate prepared.2.1
    have hv' : ∀ j, j < kv + 1 →
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id)
          ((fun j => if j = kv then selfId else vinp j) j) =
        some (.bits (vw j)
          ((fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) j (vw j))) := by
      intro j hj
      by_cases hkv : j = kv
      · subst hkv
        have h1 : vw j = w := hself
        simp only [if_pos rfl]
        rw [← h1]
        simp
      · have hjlt : j < kv := by omega
        simp only [if_neg hkv, if_neg (selfNeV j hjlt)]
        exact inputValues_bits separate (hv0 j hjlt)
    have contract := fuel_contract 1048575
      (ctx := (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context)
      (inputs := fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
        else inputValues (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bits id)
      (we := declaredWidths st) (mems := mems) (initial := env0)
      (dom := instFVars #[.fvar selfId] 0 dom2)
      (bi := binp) (vi := fun j => if j = kv then selfId else vinp j)
      (bools := bvals)
      (bits := fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n)
      hb' hv' e he
    have childEq : instFVars #[Lean.Expr.fvar selfId] 0
        (quote dom2 (fun j => .fvar (binp j))
          (fun j => if j = kv then .bvar 0 else .fvar (vinp j)) e) =
        quote (instFVars #[Lean.Expr.fvar selfId] 0 dom2)
          (fun j => .fvar (binp j))
          (fun j => .fvar ((fun j => if j = kv then selfId else vinp j) j)) e := by
      rw [instFVars_quote]
      apply quote_congr _ _ e he
      · intro j hj
        rfl
      · intro j hj
        by_cases hkv : j = kv
        · subst hkv
          simp only [if_pos rfl]
          rfl
        · simp only [if_neg hkv]
          rfl
    rw [childEq] at rc
    have lookup2 : Lookup (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id) s2 := by
      constructor
      intro id val hval
      by_cases hid : id = selfId
      · subst hid
        refine ⟨rW, visSelf, ?_⟩
        rw [s2Used]
        simp [Std.HashSet.contains_insert]
      · rw [if_neg hid] at hval
        obtain ⟨wj, hbnd, hused⟩ :=
          (lookup_of_ports prepared.1 prepared.2.1).lookup id val hval
        refine ⟨wj, visOld id wj hid hbnd, ?_⟩
        rw [s2Used]
        simp [Std.HashSet.contains_insert, hused]
    have frame := contract.frame "loop_body" false false s2 sc cw lookup2 rc
    have wiresS2 : WiresOk s2 := by
      constructor
      · rw [s2Module, mws.2.2.2, ← hr0]
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, prepared.2.1.1⟩
        intro hmem
        obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
        have := prepared.2.1.2 q hq
        rw [eq, freshR] at this
        cases this
      · intro q hq
        rw [s2Module, mws.2.2.2, ← hr0] at hq
        rw [s2Used]
        rcases List.mem_cons.mp hq with rfl | hq
        · simp [Std.HashSet.contains_insert]
        · have := prepared.2.1.2 q hq
          simp [Std.HashSet.contains_insert, this]
    have wiresSc : WiresOk sc := frame.wires wiresS2
    have wiresSt : WiresOk st := by
      constructor
      · rw [stWires]; exact wiresSc.1
      · intro q hq
        rw [stWires] at hq
        rw [stUsed]
        have := wiresSc.2 q hq
        simp [Std.HashSet.contains_insert, this]
    have rMem : ({ name := rW, ty := .bitVector w } : Sparkle.IR.AST.Port) ∈
        st.module.wires := by
      rw [stWires]
      apply frame.decls
      rw [s2Module, mws.2.2.2, ← hr0]
      exact List.mem_cons_self
    have wR : declaredWidths st rW = w := declaredWidths_agree wiresSt _ rMem
    have widths : ScalarWidthsAgree (declaredWidths st) sc := by
      intro q hq
      exact declaredWidths_agree wiresSt q (by rw [stWires]; exact hq)
    have s2Body : s2.module.body = [] := by
      rw [s2Module, mws.2.2.1, prepared.2.2.1]
      rfl
    have runs2 : Runs (declaredWidths st) mems env0 s2 env0 := by
      unfold Runs
      have hfin : s2.module.finalize.body = [] := by simp [Module.finalize, s2Body]
      rw [hfin]
      rfl
    have growth : ∀ q ∈ (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.module.wires,
        q ∈ st.module.wires := by
      intro q hq
      rw [stWires]
      exact frame.decls q (by
        rw [s2Module, mws.2.2.2, ← hr0]
        exact List.mem_cons_of_mem _ hq)
    have mixedI := prepared.1.inputs prepared.2.1 growth (declaredWidths_agree wiresSt)
    have inputsInv : Tools.ShippingUnifiedInvariant.Inputs
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id)
        (declaredWidths st) s2 env0 := by
      constructor
      intro id val hval
      by_cases hid : id = selfId
      · subst hid
        simp only [if_pos rfl] at hval
        cases hval
        refine ⟨rW, visSelf, ?_, ?_, ?_⟩
        · rw [s2Used]
          simp [Std.HashSet.contains_insert]
        · show env0 rW = (Value.bits w (BitVec.ofNat w (env0 rW))).toNat
          simp [Value.toNat, Nat.mod_eq_of_lt hstb]
        · simpa using wR
      · simp only [if_neg hid] at hval
        obtain ⟨wj, hbnd, hused, hval2, hwid⟩ :=
          (Tools.ShippingUnifiedInvariant.Inputs.of_mixed mixedI).lookup id val hval
        refine ⟨wj, visOld id wj hid hbnd, ?_, hval2, hwid⟩
        rw [s2Used]
        simp [Std.HashSet.contains_insert, hused]
    have s2Record : s2.translateRecord = {} := by
      rw [hs2]
      show s1.translateRecord = {}
      rw [hs1, CircuitM.makeWire_translateRecord, prepared.2.2.2]
      rfl
    have inv2 : Inv (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
        (fun id => if id = selfId then some (Value.bits w (BitVec.ofNat w (env0 rW)))
          else inputValues (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bools
            (prepare bools bits (bs.zip ids)
              (start (entryCompilerState false cache) declName.toString)).bits id)
        (declaredWidths st) mems env0 s2 env0 :=
      ⟨runs2, inputsInv, Records.empty s2Record, by
        intro stq hq
        rw [s2Body] at hq
        cases hq⟩
    have outcome := contract.sem "loop_body" false false s2 sc cw env0 inv2 widths rc
    obtain ⟨res, invC, valCw, fvals⟩ := outcome.execution
    have resR : res rW = env0 rW := by
      apply fvals
      rw [s2Used]
      simp [Std.HashSet.contains_insert]
    have allocSt : ∀ q ∈ st.module.wires, Sparkle.IR.NameHints.Allocated q.name := by
      intro q hq
      rw [stWires] at hq
      rcases frame.wireNames q hq with hold | halloc
      · rw [s2Module, mws.2.2.2, ← hr0] at hold
        rcases List.mem_cons.mp hold with rfl | hold2
        · rw [hr0]
          exact CircuitM.makeWire_allocated "out" (.bitVector w) true _
        · exact prepare_wires_allocated bools bits (bs.zip ids) _
            (by
              rw [show (start (entryCompilerState false cache) declName.toString).state =
                CircuitM.init declName.toString from rfl, init_wires]
              intro x hx
              cases hx)
            q hold2
      · exact halloc
    have widthRst : declaredWidths st "rst" = 0 := by
      unfold Tools.ShippingMixedOutputSoundness.declaredWidths
      cases hf : st.module.wires.find? (fun q => q.name == "rst") with
      | none => simp [hf]
      | some q =>
        have hq := List.mem_of_find?_eq_some hf
        have eq : q.name = "rst" := by simpa using List.find?_some hf
        exact absurd (eq ▸ allocSt q hq) not_allocated_rst
    have seqSc : SeqBody sc.module.finalize.body := by
      intro stq hq
      obtain ⟨l, rhs, eq, _⟩ := invC.typed stq (by
        change stq ∈ sc.module.body.reverse at hq
        exact List.mem_reverse.mp hq)
      exact Or.inl ⟨l, rhs, eq⟩
    have preAssigns : ∀ stq ∈ sc.module.finalize.body, ∃ l rhs, stq = .assign l rhs := by
      intro stq hq
      obtain ⟨l, rhs, eq, _⟩ := invC.typed stq (by
        change stq ∈ sc.module.body.reverse at hq
        exact List.mem_reverse.mp hq)
      exact ⟨l, rhs, eq⟩
    have preEq : sc.module.finalize.body = sc.module.body.reverse := by
      simp [Module.finalize]
    have rstNotW : "rst" ∉ Sparkle.IR.Reorder.writesOf sc.module.finalize.body := by
      intro hwr
      obtain ⟨stq, hst, hz⟩ := List.mem_flatMap.mp hwr
      obtain ⟨l, rhs, eq, htyped⟩ := invC.typed stq (by
        rw [preEq] at hst
        exact List.mem_reverse.mp hst)
      subst eq
      simp only [Sparkle.IR.Reorder.stmtWrites, List.mem_singleton] at hz
      subst hz
      have pos := htyped.positive
      rw [widthRst] at pos
      exact Nat.lt_irrefl 0 pos
    have runsC : evalAssigns (declaredWidths st) mems sc.module.finalize.body env0 = some res :=
      invC.runs
    have resRst : res "rst" = env0 "rst" := evalAssigns_preserved seqSc runsC rstNotW
    have smUsed : sm.usedNames = sc.usedNames := by
      rw [hrec]
      show smR.usedNames = _
      rw [hsmR, hs4]
    have cwUsed : sc.usedNames.contains cw = true := outcome.used
    have cwNotOut : cw ≠ "out" := by
      intro eq
      have hmem : sm.usedNames.contains cw = true := by rw [smUsed]; exact cwUsed
      rw [eq, freshOut] at hmem
      cases hmem
    let envF : Env := fun n => if n = "out" then res rW else res n
    have evalFull : evalAssigns (declaredWidths st) mems m.body env0 = some envF := by
      rw [mBody, ← preEq, evalAssigns_append seqSc, runsC]
      show evalAssigns _ mems
        (.register rW "clk" ("rst", .asynchronous) (.ref cw) v ::
          .assign "out" (.ref rW) :: []) res = _
      simp [evalAssigns, evalExpr, envF]
    have hcwF : envF cw = (eval bvals
        (fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) e).toNat := by
      simp only [envF, if_neg cwNotOut]
      exact valCw
    have hrstF : envF "rst" = 0 := by
      have h1 : ("rst" : String) ≠ "out" := by decide
      simp only [envF, if_neg h1]
      rw [resRst, hrst0]
    have nexts : regNexts (declaredWidths st) mems m.body envF =
        some [(rW, (eval bvals
          (fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) e).toNat)] := by
      rw [mBody, ← preEq, regNexts_skip_assigns preAssigns]
      show regNexts _ mems
        (.register rW "clk" ("rst", .asynchronous) (.ref cw) v ::
          .assign "out" (.ref rW) :: []) envF = _
      have maskEq : mask (declaredWidths st rW) (eval bvals
          (fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) e).toNat =
          (eval bvals
            (fun j n => if j = kv then BitVec.ofNat n (env0 rW) else vvals j n) e).toNat := by
        rw [wR]
        exact Nat.mod_eq_of_lt (BitVec.isLt _)
      simp [regNexts, evalExpr, hcwF, hrstF, maskEq]
    have seqM : SeqBody m.body := by
      rw [mBody, ← preEq]
      intro stq hq
      rcases List.mem_append.mp hq with hq | hq
      · exact Or.inl (preAssigns stq hq)
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inr ⟨_, _, _, _, _, rfl⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · exact Or.inl ⟨_, _, rfl⟩
          · cases hq
    have mem0 : memNexts (declaredWidths st) m.body mems envF = some mems := memNexts_seq seqM
    have scalarSt : ScalarWires st := by
      intro q hq
      rw [stWires] at hq
      apply frame.scalar
      · intro q2 hq2
        rw [s2Module, mws.2.2.2, ← hr0] at hq2
        rcases List.mem_cons.mp hq2 with rfl | hq2
        · exact Or.inr ⟨w, rfl⟩
        · exact (prepare_shape (bs.zip ids) _ (by
            intro q3 hq3
            rw [show (start (entryCompilerState false cache) declName.toString).state =
              CircuitM.init declName.toString from rfl, init_wires] at hq3
            cases hq3)).1 q2 hq2
      · exact hq
    have wm : weOf m = declaredWidths st := by
      rw [weOf_eq_moduleWidths (by
        intro q hq
        rw [mWires, List.mem_reverse] at hq
        exact scalarSt q hq)]
      exact moduleWidths_finish mWires wiresSt
    -- Sequential zero-width cleanup is the identity on the feedback shape too.
    have nodupM : (m.wires.map (·.name)).Nodup := by
      rw [mWires, List.map_reverse]
      exact nodup_reverse wiresSt.1
    have allocM : ∀ q ∈ m.wires, Sparkle.IR.NameHints.Allocated q.name := by
      intro q hq
      rw [mWires, List.mem_reverse] at hq
      exact allocSt q hq
    have outNotWire : "out" ∉ m.wires.map (·.name) := by
      intro hmem
      obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
      exact not_allocated_out (eq ▸ allocM q hq)
    have smWiresEq : sm.module.wires = st.module.wires := by
      rw [ht, emitAssign_wires, addOutput_state]
      rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).wires = mo.wires from
        fun _ _ => rfl]
    have wSm : declaredWidths sm rW = w := by
      unfold Tools.ShippingMixedOutputSoundness.declaredWidths
      rw [smWiresEq]
      exact wR
    have tyBW : ty.bitWidth = w := by
      rw [hty]
      unfold Tools.ShippingEntrySoundness.leafOutputType
      unfold Tools.ShippingMixedOutputSoundness.declaredWidths at wSm
      cases hf : sm.module.wires.find? (fun q => q.name == rW) with
      | none =>
        rw [hf] at wSm
        simp at wSm
        omega
      | some q =>
        rw [hf] at wSm
        simpa using wSm
    have mOutputs : m.outputs = [{ name := "out", ty := ty }] := by
      have outputsSm : sm.module.outputs = [] := by
        rw [hrec]
        show smR.module.outputs = _
        rw [hsmR, hs4]
        show (sc.module.addStmt _).outputs = _
        rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addStmt q).outputs = mo.outputs from
          fun _ _ => rfl, frame.outputs, s2Module, makeWire_outputs,
          (prepare_shape (bs.zip ids) _ (by
            intro q hq'
            rw [show (start (entryCompilerState false cache) declName.toString).state =
              CircuitM.init declName.toString from rfl, init_wires] at hq'
            cases hq')).2]
        rfl
      rw [hm]
      show ((addClockResetIfSequential st.module).finalize).outputs = _
      simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
      rw [ht, emitAssign_outputs, addOutput_state]
      simp [Module.addOutput, outputsSm]
    have wmOut : (Sparkle.IR.Optimize.buildWidthMap m).get? "out" = some w := by
      unfold Sparkle.IR.Optimize.buildWidthMap
      rw [Tools.ShippingPostSoundness.wmFold_notin m.wires _ "out" outNotWire, mOutputs]
      simp [Std.HashMap.get?_insert, tyBW]
    have hwPos : 0 < w := e.wf_pos he
    have bodyEq : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body := by
      unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
      split
      · rfl
      · show m.body.filterMap (Sparkle.IR.ZeroWidth.dzStmt (Sparkle.IR.Optimize.buildWidthMap m))
          = m.body
        apply Tools.ShippingPostSoundness.filterMap_eq_self
        intro stq hst
        rw [mBody] at hst
        rcases List.mem_append.mp hst with hpre | hrest
        · obtain ⟨l, rhs, rfl, htyped⟩ := invC.typed stq (List.mem_reverse.mp hpre)
          have hpos : 0 < weOf m l := by rw [wm]; exact htyped.positive
          have hg := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpos
          have htym : TypedExpr (weOf m) rhs (weOf m l) := by rw [wm]; exact htyped
          have hwmr : ∀ x ∈ Sparkle.IR.Reorder.refsOf rhs,
              Sparkle.IR.ZeroWidth.exprWidth (Sparkle.IR.Optimize.buildWidthMap m)
                (.ref x) ≠ 0 := by
            intro x hx
            have hpx := htym.refs_positive x hx
            have hgx := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpx
            simp only [Sparkle.IR.ZeroWidth.exprWidth, Std.HashMap.getD_eq_getD_getElem?,
              ← Std.HashMap.get?_eq_getElem?, hgx, Option.getD_some]
            omega
          rw [dzStmt_assign _ _ _ hg (by omega),
            Tools.ShippingTypedPostSoundness.dzExpr_typed htym _ hwmr]
        · rcases List.mem_cons.mp hrest with rfl | hrest
          · simp [Sparkle.IR.ZeroWidth.dzStmt, Sparkle.IR.ZeroWidth.dzExpr]
          · rcases List.mem_cons.mp hrest with rfl | hnil
            · rw [dzStmt_assign _ _ _ wmOut (by omega)]
              simp [Sparkle.IR.ZeroWidth.dzExpr]
            · cases hnil
    have weEq : weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m := by
      unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
      split
      · rfl
      · exact (weOf_congr_wires rfl).trans (Tools.ShippingPostSoundness.weOf_dropWires m nodupM)
    refine ⟨by rw [wm]; exact wR, bodyEq, weEq, envF, ?_, by simp [envF, resR]⟩
    rw [wm]
    unfold stepModule
    simp [evalFull, nexts, mem0, bind]

/-! ### Gate acceptance with the pushed loop binder -/

theorem synthesizeFromConst_cdo_sound {logProf declName ci bs body m d} {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    CdoPreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_cdo_sound run

theorem synthesizeCombinationalCore_cdo_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        CdoPreserves declName bs body m := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape =>
    synthesizeFromConst_cdo_sound old (shape _) (Tools.ShippingEntrySoundness.entry_kept (shape _) run).mreturns⟩

/-- Instantiation of the shifted telescope under the loop binder. -/
theorem instantiated_input_shift2 {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    (len : ids.length = bs.length) {j : Nat} (hj : j < bs.length) :
    instFVars (ids.map Lean.Expr.fvar).toArray 2 (inputExpr (bs.length + 2) j) =
      .fvar ids[j]! := by
  simp only [Tools.ShippingMixedSourceBridge.inputExpr, instFVars,
    List.size_toArray, List.length_map]
  rw [if_neg (by omega), if_pos (by omega)]
  have eq : ids.length - 1 - (bs.length + 2 - 1 - j - 2) = j := by omega
  rw [eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by omega : j < ids.length)]

theorem instantiated_input_shift3 {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    (len : ids.length = bs.length) {j : Nat} (hj : j < bs.length) :
    instFVars (ids.map Lean.Expr.fvar).toArray 3 (inputExpr (bs.length + 3) j) =
      .fvar ids[j]! := by
  simp only [Tools.ShippingMixedSourceBridge.inputExpr, instFVars,
    List.size_toArray, List.length_map]
  rw [if_neg (by omega), if_pos (by omega)]
  have eq : ids.length - 1 - (bs.length + 3 - 1 - j - 3) = j := by omega
  rw [eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by omega : j < ids.length)]

theorem instFVars_readE (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr) (w : Nat)
    (x : Lean.Expr) :
    instFVars xs d (readE dom w x) = readE (instFVars xs d dom) w (instFVars xs d x) := rfl

/-- Position plumbing for the single-slot circuit-do root. -/
theorem cdo_source {declName : Name} {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr} {m : Sparkle.IR.AST.Module} {nmR : Name} {dpos : Nat}
    {w v kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (source : CdoPreserves declName bs body m)
    (hbody : body = cdoE nmR (inputExpr bs.length dpos)
      (inputExpr (bs.length + 1) dpos) (inputExpr (bs.length + 2) dpos)
      (inputExpr (bs.length + 3) dpos) w v
      (quote (inputExpr (bs.length + 2) dpos) (fun j => inputExpr (bs.length + 2) (bpos j))
        (fun j => if j = kv then readE (inputExpr (bs.length + 2) dpos) w (.bvar 0)
          else inputExpr (bs.length + 2) (vpos j)) e))
    (hdp : dpos < bs.length)
    (hself : vw kv = w) (he : e.WF kb (kv + 1) vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ w →
      weOf m r = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun j => bools (bpos j))
            (fun j n => if j = kv then BitVec.ofNat n (env0 r) else bits (vpos j) n)
            e).toNat)], mems) ∧
        envF "out" = env0 r := by
  obtain ⟨ids, nd, len, cache, H⟩ := source
  have qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      cdoE nmR (.fvar ids[dpos]!) (.fvar ids[dpos]!) (.fvar ids[dpos]!) (.fvar ids[dpos]!) w v
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => if j = kv then readE (.fvar ids[dpos]!) w (.bvar 0)
            else .fvar ids[vpos j]!) e) := by
    rw [hbody, instFVars_cdoE, instantiated_input len hdp, instantiated_input_shift len hdp,
      instantiated_input_shift2 len hdp, instantiated_input_shift3 len hdp]
    congr 1
    rw [show (Lean.Expr.fvar ids[dpos]!) =
      instFVars (ids.map Lean.Expr.fvar).toArray 2 (inputExpr (bs.length + 2) dpos) from
      (instantiated_input_shift2 len hdp).symm]
    rw [instFVars_quote]
    apply quote_congr _ _ e he
    · intro j hj
      exact instantiated_input_shift2 len
        (List.getElem_of_getElem? (hb j hj).choose_spec).choose
    · intro j hj
      by_cases hkv : j = kv
      · subst hkv
        simp only [if_pos rfl, if_true, Nat.zero_add]
        rw [instFVars_readE, instantiated_input_shift2 len hdp]
        rfl
      · have hjlt : j < kv := by omega
        simp only [if_neg hkv]
        exact instantiated_input_shift2 len
          (List.getElem_of_getElem? (hvp j hjlt).choose_spec).choose
  obtain ⟨r, H⟩ := H nmR (.fvar ids[dpos]!) (.fvar ids[dpos]!) (.fvar ids[dpos]!)
    (.fvar ids[dpos]!) kb kv vw
    (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) e (by rfl)
    (cdoConeToLoop_fvar 0 ids[dpos]!) hself he hvlt qeq
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro bools bits env0 mems values hrst0 hstb
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  apply H (boolValues ids bools) (bitValues ids bits) env0 mems
    (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) values _ _ hrst0 hstb
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bool_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup
  · intro j hj
    obtain ⟨name, pos⟩ := hvp j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup

/-- General single-slot circuit-do endpoint at the real core entry. -/
theorem cdo_step_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {nmR : Name} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, cdoE nmR (inputExpr bs.length dpos)
      (inputExpr (bs.length + 1) dpos) (inputExpr (bs.length + 2) dpos)
      (inputExpr (bs.length + 3) dpos) w v
      (quote (inputExpr (bs.length + 2) dpos) (fun j => inputExpr (bs.length + 2) (bpos j))
        (fun j => if j = kv then readE (inputExpr (bs.length + 2) dpos) w (.bvar 0)
          else inputExpr (bs.length + 2) (vpos j)) e)))
    (hdp : dpos < bs.length)
    (hself : vw kv = w) (he : e.WF kb (kv + 1) vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r < 2 ^ w →
      weOf m r = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF, [(r, (eval (fun j => bools (bpos j))
            (fun j n => if j = kv then BitVec.ofNat n (env0 r) else bits (vpos j) n)
            e).toNat)], mems) ∧
        envF "out" = env0 r := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_cdo_sound hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have hdom : ((inputExpr bs.length dpos).isFVar || (inputExpr bs.length dpos).isBVar) = true := by
    simp only [Tools.ShippingMixedSourceBridge.inputExpr]
    rfl
  have mixedGate := cdo_term_gate (d := d)
    (by rw [definition]; exact peel) hdp hself hvlt he hb hvp
  exact cdo_source (source bs _ oldGate mixedGate) rfl hdp hself he hvlt hb hvp

theorem cdo_run_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {nmR : Name} {dpos : Nat} {w v kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, cdoE nmR (inputExpr bs.length dpos)
      (inputExpr (bs.length + 1) dpos) (inputExpr (bs.length + 2) dpos)
      (inputExpr (bs.length + 3) dpos) w v
      (quote (inputExpr (bs.length + 2) dpos) (fun j => inputExpr (bs.length + 2) (bpos j))
        (fun j => if j = kv then readE (inputExpr (bs.length + 2) dpos) w (.bvar 0)
          else inputExpr (bs.length + 2) (vpos j)) e)))
    (hdp : dpos < bs.length)
    (hself : vw kv = w) (he : e.WF kb (kv + 1) vw) (hvlt : v < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r : String),
      ∀ (bools : Nat → Nat → Bool) (bits : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat) (S : Nat → Nat),
      (∀ t stv, SourceInputs declName bs ids cache (bools (k - 1 - t)) (bits (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧ seed t stv r = stv r) →
      st0 r < 2 ^ w →
      S 0 = st0 r →
      (∀ j, j + 1 ≤ k → S (j + 1) = (eval (fun i => bools j (bpos i))
        (fun i n => if i = kv then BitVec.ofNat n (S j) else bits j (vpos i) n) e).toNat) →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j := by
  obtain ⟨ids, nd, len, cache, r, H⟩ :=
    cdo_step_of_env hr env old peel hdp hself he hvlt hb hvp
  refine ⟨ids, nd, len, cache, r, ?_⟩
  intro bools bits mems k seed st0 S hseed hst0 hS0 hSs
  apply trace_of_cycles_inv (P := fun s => s < 2 ^ w)
    (F := fun t s => (eval (fun i => bools (k - 1 - t) (bpos i))
      (fun i n => if i = kv then BitVec.ofNat n s else bits (k - 1 - t) (vpos i) n) e).toNat)
    ?_ ?_ k st0 S hst0 hS0 ?_
  · intro t stv hP
    obtain ⟨hsrc, hrst, hread⟩ := hseed t stv
    obtain ⟨-, -, -, envF, hstep, hout⟩ :=
      H (bools (k - 1 - t)) (bits (k - 1 - t)) (seed t stv) mems hsrc hrst
        (by rw [hread]; exact hP)
    refine ⟨envF, ?_, by rw [hout, hread]⟩
    rw [hread] at hstep
    exact hstep
  · intro t s hP
    exact BitVec.isLt _
  · intro j hj
    rw [hSs j hj]
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    rw [hidx]

/-- On a sequential body (any non-assign statement), the shipped merge is the
UNVALIDATED raw merge: the validated path only covers pure-assign bodies. -/
theorem mergeDuplicates_seq {m : Sparkle.IR.AST.Module}
    (h : m.body.all Sparkle.IR.RegDedup.isAssign = false) :
    Sparkle.IR.RegDedup.mergeDuplicates m = Sparkle.IR.RegDedup.mergeDuplicatesRaw m := by
  unfold Sparkle.IR.RegDedup.mergeDuplicates
  simp [h]

/-! ## The two-slot `circuit do` root -/

def cons2E (w : Nat) : Lean.Expr :=
  mkApp3 (.const ``List.cons [.succ .zero]) sort1E (bitVecE w) (consTE w)
def hl2E (w : Nat) : Lean.Expr := .app (.const ``Sparkle.Core.HList []) (cons2E w)
def sigL2E (dom : Lean.Expr) (w : Nat) : Lean.Expr :=
  mkApp2 (.const ``Sparkle.Core.Circuit.SigList []) dom (cons2E w)
def regT2E (dom : Lean.Expr) (w : Nat) : Lean.Expr :=
  mkApp4 (.const ``Sparkle.Core.Reg []) dom (hl2E w) (sigL2E dom w) (bitVecE w)
def slotT2E (dom : Lean.Expr) (w : Nat) : Lean.Expr :=
  mkApp4 (.const ``Sparkle.Core.Circuit.Slot []) dom (hl2E w) (sigL2E dom w) (bitVecE w)
def rl2E (dom : Lean.Expr) (w : Nat) (tail : Lean.Expr) : Lean.Expr :=
  mkApp4 (.const ``Sparkle.Core.RegList []) dom (hl2E w) (sigL2E dom w) tail

/-- The coerced live read of a two-slot register handle. -/
def read2E (dom : Lean.Expr) (w : Nat) (x : Lean.Expr) : Lean.Expr :=
  mkApp3 (.const ``Prod.fst [.zero, .zero]) (sigT dom w) (slotT2E dom w) x

/-- The two-slot `circuit do` exactly as the macro elaborates it over a
polymorphic domain (`nmX`/`nmY` are the user's register binder names,
`dom0`–`dom6` the domain at the successive binder depths, `outIdx` the
`bvar` index of the returned handle: 4 for the first slot, 2 for the
second). -/
def cdo2E (nmX nmY : Name) (dom0 dom1 dom2 dom3 dom4 dom5 dom6 : Lean.Expr)
    (w v0 v1 : Nat) (outE rhs0 rhs1 : Lean.Expr) : Lean.Expr :=
  mkApp8 (.const ``Sparkle.Core.runCircuitH []) dom0 (cons2E w) (sigT dom0 w)
    (mkApp2 (.const ``Sparkle.Core.instHasDomainSignal []) dom0 (bitVecE w))
    (mkApp4 (.const ``Sparkle.Core.instHListWireableConsOfWireable []) (bitVecE w) (consTE w)
      (.app (.const ``Sparkle.Core.instWireableBitVec []) (natE w))
      (mkApp4 (.const ``Sparkle.Core.instHListWireableConsOfWireable []) (bitVecE w) nilTE
        (.app (.const ``Sparkle.Core.instWireableBitVec []) (natE w))
        (.const ``Sparkle.Core.instHListWireableNil [])))
    (mkApp4 (.const ``instInhabitedProd [.zero, .zero]) (bitVecE w) (hlE w)
      (.app (.const ``BitVec.instInhabited []) (natE w))
      (mkApp4 (.const ``instInhabitedProd [.zero, .zero]) (bitVecE w) hlNilE
        (.app (.const ``BitVec.instInhabited []) (natE w))
        (.const ``instInhabitedPUnit [.succ .zero])))
    (mkApp4 (.const ``Prod.mk [.zero, .zero]) (bitVecE w) (hlE w)
      (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v0))
      (mkApp4 (.const ``Prod.mk [.zero, .zero]) (bitVecE w) hlNilE
        (mkApp2 (.const ``BitVec.ofNat []) (natE w) (natE v1)) (.const ``Unit.unit [])))
    (.lam `_cdoRegs (rl2E dom0 w (cons2E w))
      (.letE nmX (regT2E dom1 w)
        (mkApp3 (.const ``Prod.fst [.zero, .zero]) (regT2E dom1 w)
          (rl2E dom1 w (consTE w)) (.bvar 0))
        (.letE `_cdoRest_1 (rl2E dom2 w (consTE w))
          (mkApp3 (.const ``Prod.snd [.zero, .zero]) (regT2E dom2 w)
            (rl2E dom2 w (consTE w)) (.bvar 1))
          (.letE nmY (regT2E dom3 w)
            (mkApp3 (.const ``Prod.fst [.zero, .zero]) (regT2E dom3 w)
              (rl2E dom3 w nilTE) (.bvar 0))
            (mkApp6 (.const ``Sparkle.Core.Circuit.bind []) dom4 (sigL2E dom4 w)
              (.const ``Unit []) (sigT dom4 w)
              (mkApp6 (.const ``Sparkle.Core.Circuit.next []) dom4 (hl2E w) (bitVecE w)
                (sigL2E dom4 w) (.bvar 2) rhs0)
              (.lam `_cdoK (.const ``Unit [])
                (mkApp6 (.const ``Sparkle.Core.Circuit.bind []) dom5 (sigL2E dom5 w)
                  (.const ``Unit []) (sigT dom5 w)
                  (mkApp6 (.const ``Sparkle.Core.Circuit.next []) dom5 (hl2E w) (bitVecE w)
                    (sigL2E dom5 w) (.bvar 1) rhs1)
                  (.lam `_cdoK (.const ``Unit [])
                    (mkApp4 (.const ``Sparkle.Core.Circuit.pure' []) dom6 (sigL2E dom6 w)
                      (sigT dom6 w) outE)
                    .default))
                .default))
            true)
          true)
        true)
      .default)

theorem cdo2ConeToLoop_read_x {dx dy K : Nat} (dom : Lean.Expr) (w : Nat)
    (hne : dx ≠ dy) :
    cdo2ConeToLoop dx dy K 0 (read2E dom w (.bvar dx)) = some (.bvar 1) := by
  simp [read2E, mkApp3, mkApp2, mkAppB, mkApp, cdo2ConeToLoop]

theorem cdo2ConeToLoop_read_y {dx dy K : Nat} (dom : Lean.Expr) (w : Nat)
    (hne : dx ≠ dy) :
    cdo2ConeToLoop dx dy K 0 (read2E dom w (.bvar dy)) = some (.bvar 0) := by
  simp only [read2E, mkApp3, mkApp2, mkAppB, mkApp, cdo2ConeToLoop]
  rw [if_neg (by simp; omega), if_pos (by simp)]

theorem cdo2ConeToLoop_input {dx dy K n i : Nat} (h : i < n) (hK : 2 ≤ K)
    (hdx : dx < K) (hdy : dy < K) :
    cdo2ConeToLoop dx dy K 0 (inputExpr (n + K) i) = some (inputExpr (n + 2) i) := by
  show cdo2ConeToLoop dx dy K 0 (.bvar (n + K - 1 - i)) = some (.bvar (n + 2 - 1 - i))
  have key : n + K - 1 - i - K + 2 = n + 2 - 1 - i := by omega
  have hguard : (decide (0 ≤ n + K - 1 - i) && decide (n + K - 1 - i < 0 + K)) = false := by
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
    right
    omega
  simp only [cdo2ConeToLoop, hguard, Bool.false_eq_true, if_false]
  rw [if_pos (by omega : n + K - 1 - i ≥ 0 + K), key]

theorem cdo2ConeToLoop_natE (dx dy K d n : Nat) :
    cdo2ConeToLoop dx dy K d (natE n) = some (natE n) := rfl

theorem cdo2ConeToLoop_bitVecE (dx dy K d n : Nat) :
    cdo2ConeToLoop dx dy K d (bitVecE n) = some (bitVecE n) := rfl

theorem cdo2ConeToLoop_fvar (dx dy K d : Nat) (id : FVarId) :
    cdo2ConeToLoop dx dy K d (.fvar id) = some (.fvar id) := rfl

theorem cdo2ConeToLoop_sigT {dx dy K : Nat} {domS domL : Lean.Expr}
    (h : cdo2ConeToLoop dx dy K 0 domS = some domL) (w : Nat) :
    cdo2ConeToLoop dx dy K 0 (sigT domS w) = some (sigT domL w) := by
  simp [sigT, cdo2ConeToLoop, h, cdo2ConeToLoop_natE, mkApp2, mkAppB, mkApp]

/-- `cdo2ConeToLoop` distributes over the unified quote. -/
theorem cdo2ConeToLoop_quote {dx dy K : Nat} {domS domL : Lean.Expr}
    {bi vi biL viL : Nat → Lean.Expr} {kb kv : Nat} {vw : Nat → Nat}
    (hdom : cdo2ConeToLoop dx dy K 0 domS = some domL)
    (hb : ∀ j, j < kb → cdo2ConeToLoop dx dy K 0 (bi j) = some (biL j))
    (hv : ∀ j, j < kv → cdo2ConeToLoop dx dy K 0 (vi j) = some (viL j)) :
    ∀ {s : SType} (e : Term s), e.WF kb kv vw →
    cdo2ConeToLoop dx dy K 0 (quote domS bi vi e) = some (quote domL biL viL e)
  | _, .boolInput j, he => hb j he
  | _, .bitsInput _ j, he => hv j he.1
  | _, .boolLit b, _ => by
    cases b <;> simp [Tools.ShippingUnifiedSource.quote, literalE, boolName, cdo2ConeToLoop,
      cdo2ConeToLoop_natE, cdo2ConeToLoop_bitVecE, hdom, mkApp8, mkApp6, mkApp5, mkApp4,
      mkApp3, mkApp2, mkAppB, mkApp]
  | _, .bitsLit w v, _ => by
    simp [Tools.ShippingUnifiedSource.quote, quoteF, cdo2ConeToLoop, cdo2ConeToLoop_natE,
      cdo2ConeToLoop_bitVecE, hdom, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2,
      mkAppB, mkApp]
  | _, .binary op a b, he => by
    have ia := cdo2ConeToLoop_quote hdom hb hv a he.1
    have ib := cdo2ConeToLoop_quote hdom hb hv b he.2
    cases op <;> simp [Tools.ShippingUnifiedSource.quote, binE, cdo2ConeToLoop,
      cdo2ConeToLoop_natE, cdo2ConeToLoop_bitVecE, cdo2ConeToLoop_sigT hdom, hdom, sigT,
      binMethod, binInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp,
      ia, ib]
  | _, .compare op a b, he => by
    have ia := cdo2ConeToLoop_quote hdom hb hv a he.1
    have ib := cdo2ConeToLoop_quote hdom hb hv b he.2
    cases op <;> simp [Tools.ShippingUnifiedSource.quote, compareE, cdo2ConeToLoop,
      cdo2ConeToLoop_natE, cdo2ConeToLoop_bitVecE, cdo2ConeToLoop_sigT hdom, hdom, sigT,
      compareName, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia, ib]
  | _, .boolBinary op a b, he => by
    have ia := cdo2ConeToLoop_quote hdom hb hv a he.1
    have ib := cdo2ConeToLoop_quote hdom hb hv b he.2
    cases op <;> simp [Tools.ShippingUnifiedSource.quote, boolBinE, cdo2ConeToLoop,
      cdo2ConeToLoop_natE, cdo2ConeToLoop_bitVecE, cdo2ConeToLoop_sigT hdom, hdom, sigT,
      signalBoolBinName, signalBoolBinInst, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3,
      mkApp2, mkAppB, mkApp, ia, ib]
  | _, .boolNot a, he => by
    have ia := cdo2ConeToLoop_quote hdom hb hv a he
    simp [Tools.ShippingUnifiedSource.quote, boolNotE, cdo2ConeToLoop, cdo2ConeToLoop_natE,
      cdo2ConeToLoop_bitVecE, cdo2ConeToLoop_sigT hdom, hdom, sigT, mkApp8, mkApp6, mkApp5,
      mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia]
  | _, .boolEq a b, he => by
    have ia := cdo2ConeToLoop_quote hdom hb hv a he.1
    have ib := cdo2ConeToLoop_quote hdom hb hv b he.2
    simp [Tools.ShippingUnifiedSource.quote, boolEqE, cdo2ConeToLoop, cdo2ConeToLoop_natE,
      cdo2ConeToLoop_bitVecE, cdo2ConeToLoop_sigT hdom, hdom, sigT, mkApp8, mkApp6, mkApp5,
      mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia, ib]
  | s, .mux c a b, he => by
    have ic := cdo2ConeToLoop_quote hdom hb hv c he.1
    have ia := cdo2ConeToLoop_quote hdom hb hv a he.2.1
    have ib := cdo2ConeToLoop_quote hdom hb hv b he.2.2
    cases s <;> simp [Tools.ShippingUnifiedSource.quote, muxE, SType.quoteType,
      cdo2ConeToLoop, cdo2ConeToLoop_natE, cdo2ConeToLoop_bitVecE, cdo2ConeToLoop_sigT hdom,
      hdom, sigT, mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ic, ia, ib]
  | _, .setw w' a, he => by
    have ia := cdo2ConeToLoop_quote hdom hb hv a he.1
    simp [Tools.ShippingUnifiedSource.quote, setwE, cdo2ConeToLoop, cdo2ConeToLoop_natE,
      cdo2ConeToLoop_bitVecE, cdo2ConeToLoop_sigT hdom, hdom, sigT, mkApp8, mkApp6, mkApp5,
      mkApp4, mkApp3, mkApp2, mkAppB, mkApp, ia]

theorem mixed_kind_at_push2 {bs : List (Name × MixedGateBinder)} {j : Nat} {name kind}
    {k1 k2 : MixedGateBinder} (pos : bs[j]? = some (name, kind)) :
    mixedGateBVar? (((bs.map Prod.snd).toArray.push k1).push k2)
      (bs.length + 2 - 1 - j) = some kind := by
  have bound := (List.getElem_of_getElem? pos).choose
  unfold mixedGateBVar?
  simp only [Array.size_push, List.size_toArray, List.length_map]
  rw [if_pos (by omega)]
  have eq : bs.length + 1 + 1 - 1 - (bs.length + 2 - 1 - j) = j := by omega
  rw [eq]
  have hpush2 : (((bs.map Prod.snd).toArray.push k1).push k2)[j]? =
      ((bs.map Prod.snd).toArray)[j]? := by
    rw [Array.getElem?_push, if_neg (by simp; omega),
      Array.getElem?_push, if_neg (by simp; omega)]
  rw [hpush2]
  simp [List.getElem?_map, pos]

theorem mixed_kind_self0 {bs : List (Name × MixedGateBinder)}
    {k1 k2 : MixedGateBinder} :
    mixedGateBVar? (((bs.map Prod.snd).toArray.push k1).push k2) 1 = some k1 := by
  unfold mixedGateBVar?
  simp only [Array.size_push, List.size_toArray, List.length_map]
  rw [if_pos (by omega)]
  have eq : bs.length + 1 + 1 - 1 - 1 = bs.length := by omega
  rw [eq]
  rw [Array.getElem?_push,
    if_neg (by simp only [Array.size_push, List.size_toArray, List.length_map]; omega),
    Array.getElem?_push,
    if_pos (by simp only [List.size_toArray, List.length_map])]

theorem mixed_kind_self1 {bs : List (Name × MixedGateBinder)}
    {k1 k2 : MixedGateBinder} :
    mixedGateBVar? (((bs.map Prod.snd).toArray.push k1).push k2) 0 = some k2 := by
  unfold mixedGateBVar?
  simp only [Array.size_push, List.size_toArray, List.length_map]
  rw [if_pos (by omega)]
  simp

theorem input_bool_accepted_push2 {bs : List (Name × MixedGateBinder)} {j : Nat} {name}
    {k1 k2 : MixedGateBinder} (pos : bs[j]? = some (name, .bool)) :
    unifiedGateBoolBody (((bs.map Prod.snd).toArray.push k1).push k2)
      (inputExpr (bs.length + 2) j) = true := by
  change (mixedGateBVar? (((bs.map Prod.snd).toArray.push k1).push k2)
    (bs.length + 2 - 1 - j) == some MixedGateBinder.bool) = true
  rw [mixed_kind_at_push2 pos]
  rfl

theorem input_bits_accepted_push2 {bs : List (Name × MixedGateBinder)} {j : Nat} {name n}
    {k1 k2 : MixedGateBinder} (pos : bs[j]? = some (name, .bits n)) :
    unifiedGateBitsBody (((bs.map Prod.snd).toArray.push k1).push k2) n
      (inputExpr (bs.length + 2) j) = true := by
  change (mixedGateBVar? (((bs.map Prod.snd).toArray.push k1).push k2)
    (bs.length + 2 - 1 - j) == some (MixedGateBinder.bits n)) = true
  rw [mixed_kind_at_push2 pos]
  simp

theorem self0_bits_accepted {bs : List (Name × MixedGateBinder)} {w : Nat}
    {k2 : MixedGateBinder} :
    unifiedGateBitsBody (((bs.map Prod.snd).toArray.push (.bits w)).push k2) w
      (.bvar 1) = true := by
  change (mixedGateBVar? (((bs.map Prod.snd).toArray.push (.bits w)).push k2) 1 ==
    some (MixedGateBinder.bits w)) = true
  rw [mixed_kind_self0]
  simp

theorem self1_bits_accepted {bs : List (Name × MixedGateBinder)} {w : Nat}
    {k1 : MixedGateBinder} :
    unifiedGateBitsBody (((bs.map Prod.snd).toArray.push k1).push (.bits w)) w
      (.bvar 0) = true := by
  change (mixedGateBVar? (((bs.map Prod.snd).toArray.push k1).push (.bits w)) 0 ==
    some (MixedGateBinder.bits w)) = true
  rw [mixed_kind_self1]
  simp

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem canonicalCircuitDo2?_cdo2E {nmX nmY : Name}
    {dom0 dom1 dom2 dom3 dom4 dom5 dom6 outE rhs0 rhs1 cone0 cone1 : Lean.Expr}
    {w v0 v1 outIdx ret : Nat}
    (hdom : (dom0.isFVar || dom0.isBVar) = true) (hw : 0 < w)
    (hv0 : v0 < 2 ^ w) (hv1 : v1 < 2 ^ w)
    (houtE : outE = read2E dom6 w (.bvar outIdx))
    (hout : (if outIdx == 4 then some 0 else if outIdx == 2 then some 1 else none) =
      some ret)
    (hcone0 : cdo2ConeToLoop 2 0 4 0 rhs0 = some cone0)
    (hcone1 : cdo2ConeToLoop 3 1 5 0 rhs1 = some cone1) :
    canonicalCircuitDo2? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
      w v0 v1 outE rhs0 rhs1) = some (w, v0, v1, ret, cone0, cone1) := by
  subst houtE
  have hlit0 := litValue_natE w v0 hv0
  have hlit1 := litValue_natE w v1 hv1
  simp only [mkApp2, mkAppB, mkApp] at hlit0 hlit1
  -- Only spine positions the recognizer patterns inspect are unfolded;
  -- type-argument towers stay folded so the match reduction is shallow.
  dsimp only [cdo2E, cons2E, consTE, nilTE, sort1E, bitVecE, read2E,
    mkApp8, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp]
  simp only [canonicalCircuitDo2?, cdo2Slots?, cdo2Inits?, cdo2Body?, cdo2Chain?]
  simp only [hdom, if_true, canonicalNatLitValue?_natE, hlit0, hlit1,
    hout, hcone0, hcone1]
  simp [hw]

theorem instFVars_cdo2E (xs : Array Lean.Expr) (d : Nat) (nmX nmY : Name)
    (dom0 dom1 dom2 dom3 dom4 dom5 dom6 : Lean.Expr) (w v0 v1 : Nat)
    (outE rhs0 rhs1 : Lean.Expr) :
    instFVars xs d (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
      w v0 v1 outE rhs0 rhs1) =
      cdo2E nmX nmY (instFVars xs d dom0) (instFVars xs (d + 1) dom1)
        (instFVars xs (d + 2) dom2) (instFVars xs (d + 3) dom3)
        (instFVars xs (d + 4) dom4) (instFVars xs (d + 5) dom5)
        (instFVars xs (d + 6) dom6) w v0 v1 (instFVars xs (d + 6) outE)
        (instFVars xs (d + 4) rhs0) (instFVars xs (d + 5) rhs1) := rfl

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem cdo2Uncached_cdo2E (rec : TranslateFn) {nmX nmY : Name}
    {dom0 dom1 dom2 dom3 dom4 dom5 dom6 outE rhs0 rhs1 cone0 cone1 : Lean.Expr}
    {w v0 v1 outIdx ret : Nat}
    (hdom : (dom0.isFVar || dom0.isBVar) = true) (hw : 0 < w)
    (hv0 : v0 < 2 ^ w) (hv1 : v1 < 2 ^ w)
    (houtE : outE = read2E dom6 w (.bvar outIdx))
    (hout : (if outIdx == 4 then some 0 else if outIdx == 2 then some 1 else none) =
      some ret)
    (hcone0 : cdo2ConeToLoop 2 0 4 0 rhs0 = some cone0)
    (hcone1 : cdo2ConeToLoop 3 1 5 0 rhs1 = some cone1)
    (hint : String) (top named : Bool) :
    translateCircuitDo2UncachedWith rec w v0 v1 ret
        (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6 w v0 v1 outE rhs0 rhs1)
        hint top named =
      (do
        let self0 ← CompilerM.liftMetaM Lean.mkFreshFVarId
        let self1 ← CompilerM.liftMetaM Lean.mkFreshFVarId
        if self0 = self1 then
          throw (Exception.error .missing "circuit-do slot binder ids collide")
        if (← CompilerM.lookupVar self0).isSome then
          throw (Exception.error .missing "circuit-do slot-0 binder id collision")
        if (← CompilerM.lookupVar self1).isSome then
          throw (Exception.error .missing "circuit-do slot-1 binder id collision")
        let r0 ← CompilerM.makeWire hint (.bitVector w) (named := named && ret == 0)
        let r1 ← CompilerM.makeWire (hint ++ "_slot1") (.bitVector w)
          (named := named && ret == 1)
        CompilerM.bindSourceVariable self0 r0
        CompilerM.bindSourceVariable self1 r1
        let cw0 ← rec (instFVars #[.fvar self0, .fvar self1] 0 cone0) "loop_body" false false
        let cw1 ← rec (instFVars #[.fvar self0, .fvar self1] 0 cone1) "loop_body" false false
        CompilerM.emitRegisterStmt r0 "clk" "rst" (.ref cw0) v0
        CompilerM.emitRegisterStmt r1 "clk" "rst" (.ref cw1) v1
        return (if ret == 0 then r0 else r1)) := by
  unfold translateCircuitDo2UncachedWith
  rw [canonicalCircuitDo2?_cdo2E hdom hw hv0 hv1 houtE hout hcone0 hcone1]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem cdo2_step (rec : TranslateFn) {nmX nmY : Name}
    {dom0 dom1 dom2 dom3 dom4 dom5 dom6 outE rhs0 rhs1 cone0 cone1 : Lean.Expr}
    {w v0 v1 outIdx ret : Nat}
    (hdom : (dom0.isFVar || dom0.isBVar) = true) (hw : 0 < w)
    (hv0 : v0 < 2 ^ w) (hv1 : v1 < 2 ^ w)
    (houtE : outE = read2E dom6 w (.bvar outIdx))
    (hout : (if outIdx == 4 then some 0 else if outIdx == 2 then some 1 else none) =
      some ret)
    (hcone0 : cdo2ConeToLoop 2 0 4 0 rhs0 = some cone0)
    (hcone1 : cdo2ConeToLoop 3 1 5 0 rhs1 = some cone1)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec
        (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6 w v0 v1 outE rhs0 rhs1)
        hint top named =
      translateControlCachedWith (translateCircuitDo2UncachedWith rec w v0 v1 ret)
        (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6 w v0 v1 outE rhs0 rhs1)
        hint top named := by
  have shape : translateCoreShape (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = false := rfl
  have core : translateCore rec (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) hint top named = pure none := rfl
  have control : isBoolControl (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = false := rfl
  have mux : canonicalMuxType? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  have setw : canonicalSetWidth? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  have reg : canonicalRegister? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  have regEn : canonicalRegisterEnable? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  have loopReg : canonicalLoopRegister? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  have cdo1 : canonicalCircuitDo? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  have cdo2 := canonicalCircuitDo2?_cdo2E (nmX := nmX) (nmY := nmY) (dom1 := dom1)
    (dom2 := dom2) (dom3 := dom3) (dom4 := dom4) (dom5 := dom5)
    hdom hw hv0 hv1 houtE hout hcone0 hcone1
  generalize hE : cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6 w v0 v1 outE rhs0 rhs1
    = E at shape core control mux setw reg regEn loopReg cdo1 cdo2 ⊢
  have step : translateStepWith translateFallback rec E hint top named =
      translateFallback rec E hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, control, Bool.false_eq_true, if_false, mux, setw, reg,
    regEn, loopReg, cdo1, cdo2]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem unifiedRegisterRoot_cdo2E {kinds : Array MixedGateBinder} {nmX nmY : Name}
    {dom0 dom1 dom2 dom3 dom4 dom5 dom6 outE rhs0 rhs1 cone0 cone1 : Lean.Expr}
    {w v0 v1 outIdx ret : Nat}
    (hdom : (dom0.isFVar || dom0.isBVar) = true) (hw : 0 < w)
    (hv0 : v0 < 2 ^ w) (hv1 : v1 < 2 ^ w)
    (houtE : outE = read2E dom6 w (.bvar outIdx))
    (hout : (if outIdx == 4 then some 0 else if outIdx == 2 then some 1 else none) =
      some ret)
    (hcone0 : cdo2ConeToLoop 2 0 4 0 rhs0 = some cone0)
    (hcone1 : cdo2ConeToLoop 3 1 5 0 rhs1 = some cone1)
    (body0 : unifiedGateBitsBody ((kinds.push (.bits w)).push (.bits w)) w cone0 = true)
    (body1 : unifiedGateBitsBody ((kinds.push (.bits w)).push (.bits w)) w cone1 = true) :
    unifiedRegisterRoot kinds (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
      w v0 v1 outE rhs0 rhs1) = true := by
  unfold unifiedRegisterRoot
  have hreg : canonicalRegister? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  have hregEn : canonicalRegisterEnable? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  have hloop : canonicalLoopRegister? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  have hcdo1 : canonicalCircuitDo? (cdo2E nmX nmY dom0 dom1 dom2 dom3 dom4 dom5 dom6
    w v0 v1 outE rhs0 rhs1) = none := rfl
  rw [hreg, hregEn, hloop, hcdo1,
    canonicalCircuitDo2?_cdo2E hdom hw hv0 hv1 houtE hout hcone0 hcone1]
  simp [hw, body0, body1]

/-- Both circuit-do cones normalize to the two-state quote at loose-bvar
inputs (gate time): slot 0's read becomes `.bvar 1`, slot 1's `.bvar 0`. -/
theorem cdo2ConeToLoop_quote_inputs {n dpos kb kv : Nat} {vw : Nat → Nat} {w : Nat}
    {bpos vpos : Nat → Nat} (dx dy K : Nat)
    (hdp : dpos < n) (hK : 2 ≤ K) (hdx : dx < K) (hdy : dy < K) (hne : dx ≠ dy)
    (hb : ∀ j, j < kb → bpos j < n)
    (hvp : ∀ j, j < kv → vpos j < n)
    (e : Term (.bits w)) (he : e.WF kb (kv + 2) vw) :
    cdo2ConeToLoop dx dy K 0 (quote (inputExpr (n + K) dpos)
      (fun j => inputExpr (n + K) (bpos j))
      (fun j => if j = kv then read2E (inputExpr (n + K) dpos) w (.bvar dx)
        else if j = kv + 1 then read2E (inputExpr (n + K) dpos) w (.bvar dy)
        else inputExpr (n + K) (vpos j)) e) =
    some (quote (inputExpr (n + 2) dpos)
      (fun j => inputExpr (n + 2) (bpos j))
      (fun j => if j = kv then .bvar 1
        else if j = kv + 1 then .bvar 0
        else inputExpr (n + 2) (vpos j)) e) := by
  apply cdo2ConeToLoop_quote (cdo2ConeToLoop_input hdp hK hdx hdy)
    (fun j hj => cdo2ConeToLoop_input (hb j hj) hK hdx hdy) _ e he
  intro j hj
  by_cases hkv : j = kv
  · subst hkv
    simp only [if_pos rfl]
    exact cdo2ConeToLoop_read_x _ _ hne
  · by_cases hkv1 : j = kv + 1
    · subst hkv1
      simp only [if_neg (by omega : ¬(kv + 1 = kv)), if_pos rfl]
      exact cdo2ConeToLoop_read_y _ _ hne
    · have hjlt : j < kv := by omega
      simp only [if_neg hkv, if_neg hkv1]
      exact cdo2ConeToLoop_input (hvp j hjlt) hK hdx hdy

/-- Gate acceptance for the peeled two-slot circuit-do declaration. -/
theorem cdo2_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {nmX nmY : Name} {dpos : Nat} {w v0 v1 outIdx ret : Nat} {kb kv : Nat}
    {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e0 e1 : Term (.bits w)}
    (peel : mixedGatePeel d.value = some (bs, cdo2E nmX nmY
      (inputExpr bs.length dpos) (inputExpr (bs.length + 1) dpos)
      (inputExpr (bs.length + 2) dpos) (inputExpr (bs.length + 3) dpos)
      (inputExpr (bs.length + 4) dpos) (inputExpr (bs.length + 5) dpos)
      (inputExpr (bs.length + 6) dpos) w v0 v1
      (read2E (inputExpr (bs.length + 6) dpos) w (.bvar outIdx))
      (quote (inputExpr (bs.length + 4) dpos)
        (fun j => inputExpr (bs.length + 4) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 2)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 0)
          else inputExpr (bs.length + 4) (vpos j)) e0)
      (quote (inputExpr (bs.length + 5) dpos)
        (fun j => inputExpr (bs.length + 5) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 3)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 1)
          else inputExpr (bs.length + 5) (vpos j)) e1)))
    (hdp : dpos < bs.length)
    (hout : (if outIdx == 4 then some 0 else if outIdx == 2 then some 1 else none) =
      some ret)
    (hself0 : vw kv = w) (hself1 : vw (kv + 1) = w)
    (hv0 : v0 < 2 ^ w) (hv1 : v1 < 2 ^ w)
    (he0 : e0.WF kb (kv + 2) vw) (he1 : e1.WF kb (kv + 2) vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∀ isInst, mixedCertifiedShape? false [] (.defnInfo d) isInst = some (bs, cdo2E nmX nmY
      (inputExpr bs.length dpos) (inputExpr (bs.length + 1) dpos)
      (inputExpr (bs.length + 2) dpos) (inputExpr (bs.length + 3) dpos)
      (inputExpr (bs.length + 4) dpos) (inputExpr (bs.length + 5) dpos)
      (inputExpr (bs.length + 6) dpos) w v0 v1
      (read2E (inputExpr (bs.length + 6) dpos) w (.bvar outIdx))
      (quote (inputExpr (bs.length + 4) dpos)
        (fun j => inputExpr (bs.length + 4) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 2)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 0)
          else inputExpr (bs.length + 4) (vpos j)) e0)
      (quote (inputExpr (bs.length + 5) dpos)
        (fun j => inputExpr (bs.length + 5) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 3)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 1)
          else inputExpr (bs.length + 5) (vpos j)) e1)) := by
  intro isInst
  have hbLt : ∀ j, j < kb → bpos j < bs.length := fun j hj =>
    (hb j hj).elim fun name pos => (List.getElem_of_getElem? pos).choose
  have hvLt : ∀ j, j < kv → vpos j < bs.length := fun j hj =>
    (hvp j hj).elim fun name pos => (List.getElem_of_getElem? pos).choose
  have hcone0 := cdo2ConeToLoop_quote_inputs 2 0 4 hdp (by omega) (by omega) (by omega)
    (by omega) hbLt hvLt e0 he0
  have hcone1 := cdo2ConeToLoop_quote_inputs 3 1 5 hdp (by omega) (by omega) (by omega)
    (by omega) hbLt hvLt e1 he1
  have bodyOf : ∀ (e : Term (.bits w)), e.WF kb (kv + 2) vw →
      unifiedGateBitsBody (((bs.map Prod.snd).toArray.push (.bits w)).push (.bits w)) w
        (quote (inputExpr (bs.length + 2) dpos)
          (fun j => inputExpr (bs.length + 2) (bpos j))
          (fun j => if j = kv then .bvar 1
            else if j = kv + 1 then .bvar 0
            else inputExpr (bs.length + 2) (vpos j)) e) = true := by
    intro e he
    apply unified_quote_accepted
      (fun j hj => (hb j hj).elim fun name pos => input_bool_accepted_push2 pos)
      (fun j hj => by
        by_cases hkv : j = kv
        · subst hkv
          simp only [if_pos rfl]
          rw [hself0]
          exact self0_bits_accepted
        · by_cases hkv1 : j = kv + 1
          · subst hkv1
            simp only [if_neg (by omega : ¬(kv + 1 = kv)), if_pos rfl]
            rw [hself1]
            exact self1_bits_accepted
          · have hjlt : j < kv := by omega
            simp only [if_neg hkv, if_neg hkv1]
            exact (hvp j hjlt).elim fun name pos => input_bits_accepted_push2 pos)
      e he
  have hdom : ((inputExpr bs.length dpos).isFVar || (inputExpr bs.length dpos).isBVar)
      = true := by
    simp only [Tools.ShippingMixedSourceBridge.inputExpr]
    rfl
  have root := unifiedRegisterRoot_cdo2E (nmX := nmX) (nmY := nmY)
    (dom1 := inputExpr (bs.length + 1) dpos) (dom2 := inputExpr (bs.length + 2) dpos)
    (dom3 := inputExpr (bs.length + 3) dpos) (dom4 := inputExpr (bs.length + 4) dpos)
    (dom5 := inputExpr (bs.length + 5) dpos) (dom6 := inputExpr (bs.length + 6) dpos)
    (outE := read2E (inputExpr (bs.length + 6) dpos) w (.bvar outIdx))
    hdom (e0.wf_pos he0) hv0 hv1 rfl hout hcone0 hcone1
    (bodyOf e0 he0) (bodyOf e1 he1)
  simp only [mixedCertifiedShape?, Bool.false_or, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, Bool.or_true, Bool.true_or, if_true]

/-- One `stepModule` cycle of the compiled two-slot circuit-do module
(first slot returned): `out` observes register 0, and each register steps
by its cone evaluated at the current state pair (the two slots are unified
source inputs `kv` and `kv + 1`). -/
def Cdo2Preserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (nmX nmY : Name) (dom dom4 dom5 : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat)
      (binp vinp : Nat → FVarId) {w v0 v1 : Nat} (e0 e1 : Term (.bits w)),
    (dom.isFVar || dom.isBVar) = true →
    cdo2ConeToLoop 2 0 4 0 dom4 = some dom4 →
    cdo2ConeToLoop 3 1 5 0 dom5 = some dom5 →
    vw kv = w → vw (kv + 1) = w →
    e0.WF kb (kv + 2) vw → e1.WF kb (kv + 2) vw → v0 < 2 ^ w → v1 < 2 ^ w →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      cdo2E nmX nmY dom dom dom dom dom4 dom5 dom w v0 v1
        (read2E dom w (.bvar 4))
        (quote dom4 (fun j => .fvar (binp j))
          (fun j => if j = kv then read2E dom4 w (.bvar 2)
            else if j = kv + 1 then read2E dom4 w (.bvar 0)
            else .fvar (vinp j)) e0)
        (quote dom5 (fun j => .fvar (binp j))
          (fun j => if j = kv then read2E dom5 w (.bvar 3)
            else if j = kv + 1 then read2E dom5 w (.bvar 1)
            else .fvar (vinp j)) e1) →
    ∃ r0 r1 : String, r0 ≠ r1 ∧
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (mems : MEnv)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (n : Nat) → BitVec n),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨vw j, vvals j (vw j)⟩) →
    env0 "rst" = 0 → env0 r0 < 2 ^ w → env0 r1 < 2 ^ w →
    weOf m r0 = w ∧ weOf m r1 = w ∧
    (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
    weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
    ∃ envF, stepModule (weOf m) m.body env0 mems =
        some (envF,
          [(r0, (eval bvals (fun j n => if j = kv then BitVec.ofNat n (env0 r0)
            else if j = kv + 1 then BitVec.ofNat n (env0 r1) else vvals j n) e0).toNat),
           (r1, (eval bvals (fun j n => if j = kv then BitVec.ofNat n (env0 r0)
            else if j = kv + 1 then BitVec.ofNat n (env0 r1) else vvals j n) e1).toNat)],
          mems) ∧
      envF "out" = env0 r0

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 65536 in
theorem synthesizeMixedCertified_cdo2_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    Cdo2Preserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, _⟩ := synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro nmX nmY dom dom4 dom5 kb kv vw binp vinp w v0 v1 e0 e1 hdom hdom4 hdom5
    hself0 hself1 he0 he1 hv0 hv1 qeq
  have hw : 0 < w := e0.wf_pos he0
  have hconeF0 : cdo2ConeToLoop 2 0 4 0
      (quote dom4 (fun j => .fvar (binp j))
        (fun j => if j = kv then read2E dom4 w (.bvar 2)
          else if j = kv + 1 then read2E dom4 w (.bvar 0)
          else .fvar (vinp j)) e0) =
      some (quote dom4 (fun j => .fvar (binp j))
        (fun j => if j = kv then .bvar 1
          else if j = kv + 1 then .bvar 0
          else .fvar (vinp j)) e0) := by
    apply cdo2ConeToLoop_quote hdom4 (fun j _ => cdo2ConeToLoop_fvar 2 0 4 0 (binp j))
      _ e0 he0
    intro j hj
    by_cases hkv : j = kv
    · subst hkv
      simp only [if_pos rfl]
      exact cdo2ConeToLoop_read_x _ _ (by omega)
    · by_cases hkv1 : j = kv + 1
      · subst hkv1
        simp only [if_neg (by omega : ¬(kv + 1 = kv)), if_pos rfl]
        exact cdo2ConeToLoop_read_y _ _ (by omega)
      · simp only [if_neg hkv, if_neg hkv1]
        exact cdo2ConeToLoop_fvar 2 0 4 0 (vinp j)
  have hconeF1 : cdo2ConeToLoop 3 1 5 0
      (quote dom5 (fun j => .fvar (binp j))
        (fun j => if j = kv then read2E dom5 w (.bvar 3)
          else if j = kv + 1 then read2E dom5 w (.bvar 1)
          else .fvar (vinp j)) e1) =
      some (quote dom5 (fun j => .fvar (binp j))
        (fun j => if j = kv then .bvar 1
          else if j = kv + 1 then .bvar 0
          else .fvar (vinp j)) e1) := by
    apply cdo2ConeToLoop_quote hdom5 (fun j _ => cdo2ConeToLoop_fvar 3 1 5 0 (binp j))
      _ e1 he1
    intro j hj
    by_cases hkv : j = kv
    · subst hkv
      simp only [if_pos rfl]
      exact cdo2ConeToLoop_read_x _ _ (by omega)
    · by_cases hkv1 : j = kv + 1
      · subst hkv1
        simp only [if_neg (by omega : ¬(kv + 1 = kv)), if_pos rfl]
        exact cdo2ConeToLoop_read_y _ _ (by omega)
      · simp only [if_neg hkv, if_neg hkv1]
        exact cdo2ConeToLoop_fvar 3 1 5 0 (vinp j)
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) (bools := fun _ => false)
    (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨rW, sm, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have stepEq : translateExprToWire (cdo2E nmX nmY dom dom dom dom dom4 dom5 dom w v0 v1
        (read2E dom w (.bvar 4))
        (quote dom4 (fun j => .fvar (binp j))
          (fun j => if j = kv then read2E dom4 w (.bvar 2)
            else if j = kv + 1 then read2E dom4 w (.bvar 0)
            else .fvar (vinp j)) e0)
        (quote dom5 (fun j => .fvar (binp j))
          (fun j => if j = kv then read2E dom5 w (.bvar 3)
            else if j = kv + 1 then read2E dom5 w (.bvar 1)
            else .fvar (vinp j)) e1)) "out" false true =
      translateControlCachedWith (translateCircuitDo2UncachedWith
          (translateFuelFix translateStep 1048575) w v0 v1 0)
        (cdo2E nmX nmY dom dom dom dom dom4 dom5 dom w v0 v1
          (read2E dom w (.bvar 4))
          (quote dom4 (fun j => .fvar (binp j))
            (fun j => if j = kv then read2E dom4 w (.bvar 2)
              else if j = kv + 1 then read2E dom4 w (.bvar 0)
              else .fvar (vinp j)) e0)
          (quote dom5 (fun j => .fvar (binp j))
            (fun j => if j = kv then read2E dom5 w (.bvar 3)
              else if j = kv + 1 then read2E dom5 w (.bvar 1)
              else .fvar (vinp j)) e1)) "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575) _
      "out" false true = _
    rw [cdo2_step _ hdom hw hv0 hv1 rfl rfl hconeF0 hconeF1]
  rw [stepEq] at tr
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec rW rfl
    rw [record0] at dead
    simp at dead
  rw [cdo2Uncached_cdo2E _ hdom hw hv0 hv1 rfl rfl hconeF0 hconeF1] at missRun

  obtain ⟨self0, sfa, rfresh0, missRun⟩ := Returns.bind missRun
  have hsfa : sfa = _ := Returns.liftMetaM rfresh0
  subst hsfa
  obtain ⟨self1, sfb, rfresh1, missRun⟩ := Returns.bind missRun
  have hsfb : sfb = _ := Returns.liftMetaM rfresh1
  subst hsfb
  by_cases hneSelf : self0 = self1
  · rw [if_pos hneSelf] at missRun
    exact (Returns.throw missRun).elim
  rw [if_neg hneSelf] at missRun
  obtain ⟨aOpt0, sg0, rlook0, missRun⟩ := Returns.bind missRun
  obtain ⟨hsg0, hvisEq0⟩ := lookupVar_returns rlook0
  subst hsg0
  cases hopt0 : aOpt0.isSome with
  | true =>
    rw [hopt0] at missRun
    simp only [if_true] at missRun
    obtain ⟨_, _, hthrow, _⟩ := Returns.bind missRun
    exact (Returns.throw hthrow).elim
  | false =>
  rw [hopt0] at missRun
  simp only [Bool.false_eq_true, if_false] at missRun
  obtain ⟨aOpt1, sg1, rlook1, missRun⟩ := Returns.bind missRun
  obtain ⟨hsg1, hvisEq1⟩ := lookupVar_returns rlook1
  subst hsg1
  cases hopt1 : aOpt1.isSome with
  | true =>
    rw [hopt1] at missRun
    simp only [if_true] at missRun
    obtain ⟨_, _, hthrow, _⟩ := Returns.bind missRun
    exact (Returns.throw hthrow).elim
  | false =>
  rw [hopt1] at missRun
  simp only [Bool.false_eq_true, if_false] at missRun
  have hvis0 : Tools.ShippingBindingsSoundness.visible
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings
      self0 = none := by
    rw [← hvisEq0]
    exact Option.not_isSome_iff_eq_none.mp (by simp [hopt0])
  have hvis1 : Tools.ShippingBindingsSoundness.visible
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings
      self1 = none := by
    rw [← hvisEq1]
    exact Option.not_isSome_iff_eq_none.mp (by simp [hopt1])
  obtain ⟨r0w, s1a, rmk0, missRun⟩ := Returns.bind missRun
  obtain ⟨hr0w, hs1a⟩ := makeWire_returns rmk0
  obtain ⟨r1w, s1b, rmk1, missRun⟩ := Returns.bind missRun
  obtain ⟨hr1w, hs1b⟩ := makeWire_returns rmk1
  obtain ⟨ub0, s2a, rbind0, missRun⟩ := Returns.bind missRun
  have hs2a := bindSourceVariable_returns rbind0
  obtain ⟨ub1, s2b, rbind1, missRun⟩ := Returns.bind missRun
  have hs2b := bindSourceVariable_returns rbind1
  obtain ⟨cw0, sc0, rc0, missRun⟩ := Returns.bind missRun
  obtain ⟨cw1, sc1, rc1, missRun⟩ := Returns.bind missRun
  obtain ⟨ue0, s4a, remit0, missRun⟩ := Returns.bind missRun
  have hs4a := emitRegisterStmt_returns remit0
  obtain ⟨ue1, s4b, remit1, rpure⟩ := Returns.bind missRun
  have hs4b := emitRegisterStmt_returns remit1
  obtain ⟨hrWeq, hsmR⟩ := Returns.pure rpure
  have hrW0 : rW = r0w := by
    rw [hrWeq]
    rfl
  have hrec := recordTranslation_returns record

  -- Static shapes.
  have stBody : st.module.body =
      .assign "out" (.ref rW) ::
        .register r1w "clk" ("rst", .asynchronous) (.ref cw1) v1 ::
          .register r0w "clk" ("rst", .asynchronous) (.ref cw0) v0 :: sc1.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state]
    show _ :: (sm.module.addOutput _).body = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).body = mo.body from
      fun _ _ => rfl, hrec]
    show _ :: smR.module.body = _
    rw [hsmR, hs4b, hs4a]
    rfl
  have stWires : st.module.wires = sc1.module.wires := by
    rw [ht, emitAssign_wires, addOutput_state]
    show (sm.module.addOutput _).wires = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).wires = mo.wires from
      fun _ _ => rfl, hrec]
    show smR.module.wires = _
    rw [hsmR, hs4b, hs4a]
    rfl
  have stUsed : st.usedNames = sc1.usedNames.insert "out" := by
    rw [ht, emitAssign_usedNames, addOutput_state]
    show sm.usedNames.insert "out" = _
    rw [hrec]
    show smR.usedNames.insert "out" = _
    rw [hsmR, hs4b, hs4a]
  have mBody : m.body = sc1.module.body.reverse ++
      [.register r0w "clk" ("rst", .asynchronous) (.ref cw0) v0,
       .register r1w "clk" ("rst", .asynchronous) (.ref cw1) v1,
       .assign "out" (.ref rW)] := by
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).body = _
    simp only [Module.finalize, (addClockReset_facts st.module).1, stBody]
    simp
  have mWires : m.wires = st.module.wires.reverse := by
    rw [hm]; simp only [Module.finalize, (addClockReset_facts st.module).2.1]
  have hne01 : r0w ≠ r1w := by
    intro heq
    have mws0 := CircuitM.makeWire_spec "out" (.bitVector w) (true && 0 == 0)
      (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state
    have mws1 := CircuitM.makeWire_spec ("out" ++ "_slot1") (.bitVector w) (true && 0 == 1)
      s1a
    have fresh1 : s1a.usedNames.contains r1w = false := by rw [hr1w]; exact mws1.1
    have used0 : s1a.usedNames.contains r0w = true := by
      rw [hs1a, mws0.2.1, ← hr0w]
      simp [Std.HashSet.contains_insert]
    rw [← heq, used0] at fresh1
    cases fresh1
  refine ⟨r0w, r1w, hne01, ?_⟩
  intro bools bits env0 mems bvals vvals a p adm hb0 hv0v hrst0 hst0b hst1b

  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [pc] at rc0 rc1
  rw [ps] at hr0w hs1a
  rw [pc, ps] at hvis0 hvis1
  have mws0 := CircuitM.makeWire_spec "out" (.bitVector w) (true && 0 == 0)
    (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state
  have mws1 := CircuitM.makeWire_spec ("out" ++ "_slot1") (.bitVector w) (true && 0 == 1) s1a
  have fresh0 : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.usedNames.contains r0w
      = false := by rw [hr0w]; exact mws0.1
  have fresh1a : s1a.usedNames.contains r1w = false := by rw [hr1w]; exact mws1.1
  have s1aUsed : s1a.usedNames = (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.usedNames.insert r0w := by
    rw [hs1a, mws0.2.1, ← hr0w]
  have hnames : self0.name ≠ self1.name := fun h => hneSelf (fvarId_name_inj h)
  have hvisVar0 : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup self0
      = none := by
    revert hvis0
    unfold Tools.ShippingBindingsSoundness.visible
    cases (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup self0
    · intro _; rfl
    · intro hcon; cases hcon
  have hvisPer0 : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.get?
      self0.name = none := by
    revert hvis0
    unfold Tools.ShippingBindingsSoundness.visible
    rw [hvisVar0]
    intro h; exact h
  have hvisVar1 : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup self1
      = none := by
    revert hvis1
    unfold Tools.ShippingBindingsSoundness.visible
    cases (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup self1
    · intro _; rfl
    · intro hcon; cases hcon
  have hvisPer1 : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.get?
      self1.name = none := by
    revert hvis1
    unfold Tools.ShippingBindingsSoundness.visible
    rw [hvisVar1]
    intro h; exact h
  have selfNe0 : ∀ id, Tools.ShippingBindingsSoundness.visible
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings id ≠
      none → id ≠ self0 := by
    intro id hne heq
    subst heq
    exact hne hvis0
  have selfNe1 : ∀ id, Tools.ShippingBindingsSoundness.visible
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings id ≠
      none → id ≠ self1 := by
    intro id hne heq
    subst heq
    exact hne hvis1
  have s2bBind : s2b.sourceBindings = ((prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.insert
      self0.name r0w).insert self1.name r1w := by
    rw [hs2b]
    show s2a.sourceBindings.insert self1.name r1w = _
    rw [hs2a]
    show (s1b.sourceBindings.insert self0.name r0w).insert self1.name r1w = _
    rw [hs1b, CircuitM.makeWire_sourceBindings, hs1a, CircuitM.makeWire_sourceBindings]
  have s2bUsed : s2b.usedNames = ((prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.usedNames.insert
      r0w).insert r1w := by
    rw [hs2b]
    show s2a.usedNames = _
    rw [hs2a]
    show s1b.usedNames = _
    rw [hs1b, mws1.2.1, ← hr1w, s1aUsed]
  have s2bModule : s2b.module = (CircuitM.makeWire ("out" ++ "_slot1") (.bitVector w)
      (true && 0 == 1) s1a).2.module := by
    rw [hs2b]
    show s2a.module = _
    rw [hs2a]
    show s1b.module = _
    rw [hs1b]
  have s2bWires : s2b.module.wires = { name := r1w, ty := .bitVector w } ::
      { name := r0w, ty := .bitVector w } :: (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.module.wires := by
    rw [s2bModule, mws1.2.2.2, ← hr1w, hs1a, mws0.2.2.2, ← hr0w]
  have s2bBody : s2b.module.body = [] := by
    rw [s2bModule, mws1.2.2.1, hs1a, mws0.2.2.1, prepared.2.2.1]
    rfl
  have s2bRecord : s2b.translateRecord = {} := by
    rw [hs2b]
    show s2a.translateRecord = {}
    rw [hs2a]
    show s1b.translateRecord = {}
    rw [hs1b, CircuitM.makeWire_translateRecord, hs1a, CircuitM.makeWire_translateRecord,
      prepared.2.2.2]
    rfl
  have visSelf0 : Tools.ShippingBindingsSoundness.visible
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      s2b.sourceBindings self0 = some r0w := by
    unfold Tools.ShippingBindingsSoundness.visible
    rw [hvisVar0, s2bBind]
    have h1 : (self1.name == self0.name) = false := by
      simp only [beq_eq_false_iff_ne]
      exact fun h => hnames h.symm
    simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, h1,
      Bool.false_eq_true, if_false, beq_self_eq_true, if_true]
  have visSelf1 : Tools.ShippingBindingsSoundness.visible
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      s2b.sourceBindings self1 = some r1w := by
    unfold Tools.ShippingBindingsSoundness.visible
    rw [hvisVar1, s2bBind]
    simp [Std.HashMap.getElem?_insert]
  have visOld2 : ∀ id z, id ≠ self0 → id ≠ self1 →
      Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings
        id = some z →
      Tools.ShippingBindingsSoundness.visible
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).context
        s2b.sourceBindings id = some z := by
    intro id z hne0 hne1 hz
    unfold Tools.ShippingBindingsSoundness.visible at hz ⊢
    rw [s2bBind]
    cases hvm : (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context.varMap.lookup id with
    | some u => rw [hvm] at hz; exact hz
    | none =>
      rw [hvm] at hz
      have hz' : (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.get?
          id.name = some z := hz
      have hname0 : ¬ (self0.name = id.name) := fun h => hne0 (fvarId_name_inj h.symm)
      have hname1 : ¬ (self1.name = id.name) := fun h => hne1 (fvarId_name_inj h.symm)
      show (((prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.sourceBindings.insert
          self0.name r0w).insert self1.name r1w).get? id.name = some z
      simpa [Std.HashMap.getElem?_insert, hname0, hname1] using hz'

  have selfNeB0 : ∀ j, j < kb → binp j ≠ self0 := by
    intro j hj
    obtain ⟨wj, hbnd, -⟩ := prepared.1.bool (binp j) (bvals j) (hb0 j hj)
    exact selfNe0 _ (by rw [hbnd]; simp)
  have selfNeB1 : ∀ j, j < kb → binp j ≠ self1 := by
    intro j hj
    obtain ⟨wj, hbnd, -⟩ := prepared.1.bool (binp j) (bvals j) (hb0 j hj)
    exact selfNe1 _ (by rw [hbnd]; simp)
  have selfNeV0 : ∀ j, j < kv → vinp j ≠ self0 := by
    intro j hj
    obtain ⟨wj, hbnd, -⟩ := prepared.1.bits (vinp j) (vw j) (vvals j (vw j)) (hv0v j hj)
    exact selfNe0 _ (by rw [hbnd]; simp)
  have selfNeV1 : ∀ j, j < kv → vinp j ≠ self1 := by
    intro j hj
    obtain ⟨wj, hbnd, -⟩ := prepared.1.bits (vinp j) (vw j) (vvals j (vw j)) (hv0v j hj)
    exact selfNe1 _ (by rw [hbnd]; simp)
  have hb2 : ∀ j, j < kb →
      (fun id => if id = self0 then some (Value.bits w (BitVec.ofNat w (env0 r0w)))
        else if id = self1 then some (Value.bits w (BitVec.ofNat w (env0 r1w)))
        else inputValues (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bits id) (binp j) =
      some (.bool (bvals j)) := by
    intro j hj
    simp only [if_neg (selfNeB0 j hj), if_neg (selfNeB1 j hj)]
    exact inputValues_bool (hb0 j hj)
  have separate := prepared.1.separate prepared.2.1
  have hv2 : ∀ j, j < kv + 2 →
      (fun id => if id = self0 then some (Value.bits w (BitVec.ofNat w (env0 r0w)))
        else if id = self1 then some (Value.bits w (BitVec.ofNat w (env0 r1w)))
        else inputValues (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bits id)
        ((fun j => if j = kv then self0 else if j = kv + 1 then self1 else vinp j) j) =
      some (.bits (vw j)
        ((fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
          else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n) j (vw j))) := by
    intro j hj
    by_cases hkv : j = kv
    · subst hkv
      have h1 : vw j = w := hself0
      simp only [if_pos rfl]
      rw [← h1]
      simp
    · by_cases hkv1 : j = kv + 1
      · subst hkv1
        have h1 : vw (kv + 1) = w := hself1
        simp only [if_neg hkv, if_pos rfl, eq_self_iff_true, if_true]
        rw [if_neg (show ¬(self1 = self0) from fun h2 => hneSelf h2.symm)]
        rw [← h1]
      · have hjlt : j < kv := by omega
        simp only [if_neg hkv, if_neg hkv1, if_neg (selfNeV0 j hjlt),
          if_neg (selfNeV1 j hjlt)]
        exact inputValues_bits separate (hv0v j hjlt)
  have contract0 := fuel_contract 1048575
    (ctx := (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context)
    (inputs := fun id => if id = self0 then some (Value.bits w (BitVec.ofNat w (env0 r0w)))
      else if id = self1 then some (Value.bits w (BitVec.ofNat w (env0 r1w)))
      else inputValues (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits id)
    (we := declaredWidths st) (mems := mems) (initial := env0)
    (dom := instFVars #[.fvar self0, .fvar self1] 0 dom4)
    (bi := binp)
    (vi := fun j => if j = kv then self0 else if j = kv + 1 then self1 else vinp j)
    (bools := bvals)
    (bits := fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
      else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n)
    hb2 hv2 e0 he0
  have contract1 := fuel_contract 1048575
    (ctx := (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context)
    (inputs := fun id => if id = self0 then some (Value.bits w (BitVec.ofNat w (env0 r0w)))
      else if id = self1 then some (Value.bits w (BitVec.ofNat w (env0 r1w)))
      else inputValues (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).bools
        (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bits id)
    (we := declaredWidths st) (mems := mems) (initial := env0)
    (dom := instFVars #[.fvar self0, .fvar self1] 0 dom5)
    (bi := binp)
    (vi := fun j => if j = kv then self0 else if j = kv + 1 then self1 else vinp j)
    (bools := bvals)
    (bits := fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
      else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n)
    hb2 hv2 e1 he1
  have childEq0 : instFVars #[Lean.Expr.fvar self0, Lean.Expr.fvar self1] 0
      (quote dom4 (fun j => .fvar (binp j))
        (fun j => if j = kv then .bvar 1
          else if j = kv + 1 then .bvar 0
          else .fvar (vinp j)) e0) =
      quote (instFVars #[Lean.Expr.fvar self0, Lean.Expr.fvar self1] 0 dom4)
        (fun j => .fvar (binp j))
        (fun j => .fvar ((fun j => if j = kv then self0
          else if j = kv + 1 then self1 else vinp j) j)) e0 := by
    rw [instFVars_quote]
    apply quote_congr _ _ e0 he0
    · intro j hj
      rfl
    · intro j hj
      by_cases hkv : j = kv
      · subst hkv
        simp only [if_pos rfl]
        rfl
      · by_cases hkv1 : j = kv + 1
        · subst hkv1
          simp only [if_neg (by omega : ¬(kv + 1 = kv)), if_pos rfl]
          rfl
        · simp only [if_neg hkv, if_neg hkv1]
          rfl
  have childEq1 : instFVars #[Lean.Expr.fvar self0, Lean.Expr.fvar self1] 0
      (quote dom5 (fun j => .fvar (binp j))
        (fun j => if j = kv then .bvar 1
          else if j = kv + 1 then .bvar 0
          else .fvar (vinp j)) e1) =
      quote (instFVars #[Lean.Expr.fvar self0, Lean.Expr.fvar self1] 0 dom5)
        (fun j => .fvar (binp j))
        (fun j => .fvar ((fun j => if j = kv then self0
          else if j = kv + 1 then self1 else vinp j) j)) e1 := by
    rw [instFVars_quote]
    apply quote_congr _ _ e1 he1
    · intro j hj
      rfl
    · intro j hj
      by_cases hkv : j = kv
      · subst hkv
        simp only [if_pos rfl]
        rfl
      · by_cases hkv1 : j = kv + 1
        · subst hkv1
          simp only [if_neg (by omega : ¬(kv + 1 = kv)), if_pos rfl]
          rfl
        · simp only [if_neg hkv, if_neg hkv1]
          rfl
  rw [childEq0] at rc0
  rw [childEq1] at rc1

  have lookup2b : Lookup (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context
      (fun id => if id = self0 then some (Value.bits w (BitVec.ofNat w (env0 r0w)))
        else if id = self1 then some (Value.bits w (BitVec.ofNat w (env0 r1w)))
        else inputValues (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bits id) s2b := by
    constructor
    intro id val hval
    by_cases hid0 : id = self0
    · subst hid0
      refine ⟨r0w, visSelf0, ?_⟩
      rw [s2bUsed]
      simp [Std.HashSet.contains_insert]
    · by_cases hid1 : id = self1
      · subst hid1
        refine ⟨r1w, visSelf1, ?_⟩
        rw [s2bUsed]
        simp [Std.HashSet.contains_insert]
      · rw [if_neg hid0, if_neg hid1] at hval
        obtain ⟨wj, hbnd, hused⟩ :=
          (lookup_of_ports prepared.1 prepared.2.1).lookup id val hval
        refine ⟨wj, visOld2 id wj hid0 hid1 hbnd, ?_⟩
        rw [s2bUsed]
        simp [Std.HashSet.contains_insert, hused]
  have frame0 := contract0.frame "loop_body" false false s2b sc0 cw0 lookup2b rc0
  have lookupSc0 : Lookup (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context
      (fun id => if id = self0 then some (Value.bits w (BitVec.ofNat w (env0 r0w)))
        else if id = self1 then some (Value.bits w (BitVec.ofNat w (env0 r1w)))
        else inputValues (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bits id) sc0 := by
    constructor
    intro id val hval
    obtain ⟨wj, hbnd, hused⟩ := lookup2b.lookup id val hval
    refine ⟨wj, ?_, frame0.used wj hused⟩
    rw [frame0.bindings]
    exact hbnd
  have frame1 := contract1.frame "loop_body" false false sc0 sc1 cw1 lookupSc0 rc1
  have wiresS2b : WiresOk s2b := by
    constructor
    · rw [s2bWires]
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ?_, prepared.2.1.1⟩
      · intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem2
        · exact hne01 heq.symm
        · obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem2
          have := prepared.2.1.2 q hq
          have hin : s1a.usedNames.contains r1w = true := by
            rw [s1aUsed]
            simp [Std.HashSet.contains_insert, eq ▸ this]
          rw [fresh1a] at hin
          cases hin
      · intro hmem
        obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
        have := prepared.2.1.2 q hq
        rw [eq, fresh0] at this
        cases this
    · intro q hq
      rw [s2bWires] at hq
      rw [s2bUsed]
      rcases List.mem_cons.mp hq with rfl | hq
      · simp [Std.HashSet.contains_insert]
      · rcases List.mem_cons.mp hq with rfl | hq
        · simp [Std.HashSet.contains_insert]
        · have := prepared.2.1.2 q hq
          simp [Std.HashSet.contains_insert, this]
  have wiresSc1 : WiresOk sc1 := frame1.wires (frame0.wires wiresS2b)
  have wiresSt : WiresOk st := by
    constructor
    · rw [stWires]; exact wiresSc1.1
    · intro q hq
      rw [stWires] at hq
      rw [stUsed]
      have := wiresSc1.2 q hq
      simp [Std.HashSet.contains_insert, this]
  have rMem0 : ({ name := r0w, ty := .bitVector w } : Sparkle.IR.AST.Port) ∈
      st.module.wires := by
    rw [stWires]
    apply frame1.decls
    apply frame0.decls
    rw [s2bWires]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have rMem1 : ({ name := r1w, ty := .bitVector w } : Sparkle.IR.AST.Port) ∈
      st.module.wires := by
    rw [stWires]
    apply frame1.decls
    apply frame0.decls
    rw [s2bWires]
    exact List.mem_cons_self
  have wR0 : declaredWidths st r0w = w := declaredWidths_agree wiresSt _ rMem0
  have wR1 : declaredWidths st r1w = w := declaredWidths_agree wiresSt _ rMem1
  have widths0 : ScalarWidthsAgree (declaredWidths st) sc0 := by
    intro q hq
    exact declaredWidths_agree wiresSt q (by rw [stWires]; exact frame1.decls q hq)
  have widths1 : ScalarWidthsAgree (declaredWidths st) sc1 := by
    intro q hq
    exact declaredWidths_agree wiresSt q (by rw [stWires]; exact hq)
  have runs2b : Runs (declaredWidths st) mems env0 s2b env0 := by
    unfold Runs
    have hfin : s2b.module.finalize.body = [] := by simp [Module.finalize, s2bBody]
    rw [hfin]
    rfl
  have growth : ∀ q ∈ (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.wires,
      q ∈ st.module.wires := by
    intro q hq
    rw [stWires]
    apply frame1.decls
    apply frame0.decls
    rw [s2bWires]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)
  have mixedI := prepared.1.inputs prepared.2.1 growth (declaredWidths_agree wiresSt)
  have inputsInv : Tools.ShippingUnifiedInvariant.Inputs
      (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).context
      (fun id => if id = self0 then some (Value.bits w (BitVec.ofNat w (env0 r0w)))
        else if id = self1 then some (Value.bits w (BitVec.ofNat w (env0 r1w)))
        else inputValues (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bits id)
      (declaredWidths st) s2b env0 := by
    constructor
    intro id val hval
    by_cases hid0 : id = self0
    · subst hid0
      simp only [if_pos rfl] at hval
      cases hval
      refine ⟨r0w, visSelf0, ?_, ?_, ?_⟩
      · rw [s2bUsed]
        simp [Std.HashSet.contains_insert]
      · show env0 r0w = (Value.bits w (BitVec.ofNat w (env0 r0w))).toNat
        simp [Value.toNat, Nat.mod_eq_of_lt hst0b]
      · simpa using wR0
    · by_cases hid1 : id = self1
      · subst hid1
        simp only [if_neg hid0, if_pos rfl] at hval
        cases hval
        refine ⟨r1w, visSelf1, ?_, ?_, ?_⟩
        · rw [s2bUsed]
          simp [Std.HashSet.contains_insert]
        · show env0 r1w = (Value.bits w (BitVec.ofNat w (env0 r1w))).toNat
          simp [Value.toNat, Nat.mod_eq_of_lt hst1b]
        · simpa using wR1
      · simp only [if_neg hid0, if_neg hid1] at hval
        obtain ⟨wj, hbnd, hused, hval2, hwid⟩ :=
          (Tools.ShippingUnifiedInvariant.Inputs.of_mixed mixedI).lookup id val hval
        refine ⟨wj, visOld2 id wj hid0 hid1 hbnd, ?_, hval2, hwid⟩
        rw [s2bUsed]
        simp [Std.HashSet.contains_insert, hused]
  have inv2b : Inv (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context
      (fun id => if id = self0 then some (Value.bits w (BitVec.ofNat w (env0 r0w)))
        else if id = self1 then some (Value.bits w (BitVec.ofNat w (env0 r1w)))
        else inputValues (prepare bools bits (bs.zip ids)
          (start (entryCompilerState false cache) declName.toString)).bools
          (prepare bools bits (bs.zip ids)
            (start (entryCompilerState false cache) declName.toString)).bits id)
      (declaredWidths st) mems env0 s2b env0 :=
    ⟨runs2b, inputsInv, Records.empty s2bRecord, by
      intro stq hq
      rw [s2bBody] at hq
      cases hq⟩
  have outcome0 := contract0.sem "loop_body" false false s2b sc0 cw0 env0 inv2b widths0 rc0
  obtain ⟨res0, invC0, valCw0, fvals0⟩ := outcome0.execution
  have outcome1 := contract1.sem "loop_body" false false sc0 sc1 cw1 res0 invC0 widths1 rc1
  obtain ⟨res1, invC1, valCw1, fvals1⟩ := outcome1.execution

  have usedR0s2b : s2b.usedNames.contains r0w = true := by
    rw [s2bUsed]
    simp [Std.HashSet.contains_insert]
  have usedR1s2b : s2b.usedNames.contains r1w = true := by
    rw [s2bUsed]
    simp [Std.HashSet.contains_insert]
  have resR0 : res1 r0w = env0 r0w :=
    (fvals1 r0w (frame0.used r0w usedR0s2b)).trans (fvals0 r0w usedR0s2b)
  have resR1 : res1 r1w = env0 r1w :=
    (fvals1 r1w (frame0.used r1w usedR1s2b)).trans (fvals0 r1w usedR1s2b)
  have allocSt : ∀ q ∈ st.module.wires, Sparkle.IR.NameHints.Allocated q.name := by
    intro q hq
    rw [stWires] at hq
    rcases frame1.wireNames q hq with hold1 | halloc
    · rcases frame0.wireNames q hold1 with hold0 | halloc
      · rw [s2bWires] at hold0
        rcases List.mem_cons.mp hold0 with rfl | hold0
        · rw [hr1w]
          exact CircuitM.makeWire_allocated ("out" ++ "_slot1") (.bitVector w) (true && 0 == 1) _
        · rcases List.mem_cons.mp hold0 with rfl | hold0
          · rw [hr0w]
            exact CircuitM.makeWire_allocated "out" (.bitVector w) (true && 0 == 0) _
          · exact prepare_wires_allocated bools bits (bs.zip ids) _
              (by
                rw [show (start (entryCompilerState false cache) declName.toString).state =
                  CircuitM.init declName.toString from rfl, init_wires]
                intro x hx
                cases hx)
              q hold0
      · exact halloc
    · exact halloc
  have widthRst : declaredWidths st "rst" = 0 := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    cases hf : st.module.wires.find? (fun q => q.name == "rst") with
    | none => simp [hf]
    | some q =>
      have hq := List.mem_of_find?_eq_some hf
      have eq : q.name = "rst" := by simpa using List.find?_some hf
      exact absurd (eq ▸ allocSt q hq) not_allocated_rst
  have seqSc1 : SeqBody sc1.module.finalize.body := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := invC1.typed stq (by
      change stq ∈ sc1.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact Or.inl ⟨l, rhs, eq⟩
  have preAssigns : ∀ stq ∈ sc1.module.finalize.body, ∃ l rhs, stq = .assign l rhs := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := invC1.typed stq (by
      change stq ∈ sc1.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact ⟨l, rhs, eq⟩
  have preEq : sc1.module.finalize.body = sc1.module.body.reverse := by
    simp [Module.finalize]
  have rstNotW : "rst" ∉ Sparkle.IR.Reorder.writesOf sc1.module.finalize.body := by
    intro hwr
    obtain ⟨stq, hst, hz⟩ := List.mem_flatMap.mp hwr
    obtain ⟨l, rhs, eq, htyped⟩ := invC1.typed stq (by
      rw [preEq] at hst
      exact List.mem_reverse.mp hst)
    subst eq
    simp only [Sparkle.IR.Reorder.stmtWrites, List.mem_singleton] at hz
    subst hz
    have pos := htyped.positive
    rw [widthRst] at pos
    exact Nat.lt_irrefl 0 pos
  have runsC : evalAssigns (declaredWidths st) mems sc1.module.finalize.body env0 =
      some res1 := invC1.runs
  have resRst : res1 "rst" = env0 "rst" := evalAssigns_preserved seqSc1 runsC rstNotW
  have smUsed : sm.usedNames = sc1.usedNames := by
    rw [hrec]
    show smR.usedNames = _
    rw [hsmR, hs4b, hs4a]
  have cw0Used : sc0.usedNames.contains cw0 = true := outcome0.used
  have cw1Used : sc1.usedNames.contains cw1 = true := outcome1.used
  have cw0NotOut : cw0 ≠ "out" := by
    intro eq
    have hmem : sm.usedNames.contains cw0 = true := by
      rw [smUsed]
      exact frame1.used cw0 cw0Used
    rw [eq, freshOut] at hmem
    cases hmem
  have cw1NotOut : cw1 ≠ "out" := by
    intro eq
    have hmem : sm.usedNames.contains cw1 = true := by
      rw [smUsed]
      exact cw1Used
    rw [eq, freshOut] at hmem
    cases hmem
  let envF : Env := fun n => if n = "out" then res1 rW else res1 n
  have evalFull : evalAssigns (declaredWidths st) mems m.body env0 = some envF := by
    rw [mBody, ← preEq, evalAssigns_append seqSc1, runsC]
    show evalAssigns _ mems
      (.register r0w "clk" ("rst", .asynchronous) (.ref cw0) v0 ::
        .register r1w "clk" ("rst", .asynchronous) (.ref cw1) v1 ::
          .assign "out" (.ref rW) :: []) res1 = _
    simp [evalAssigns, evalExpr, envF]
  have hcw0F : envF cw0 = (eval bvals
      (fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
        else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n) e0).toNat := by
    simp only [envF, if_neg cw0NotOut]
    exact (fvals1 cw0 cw0Used).trans valCw0
  have hcw1F : envF cw1 = (eval bvals
      (fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
        else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n) e1).toNat := by
    simp only [envF, if_neg cw1NotOut]
    exact valCw1
  have hrstF : envF "rst" = 0 := by
    have h1 : ("rst" : String) ≠ "out" := by decide
    simp only [envF, if_neg h1]
    rw [resRst, hrst0]
  have nexts : regNexts (declaredWidths st) mems m.body envF =
      some [(r0w, (eval bvals
        (fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
          else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n) e0).toNat),
        (r1w, (eval bvals
          (fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
            else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n) e1).toNat)] := by
    rw [mBody, ← preEq, regNexts_skip_assigns preAssigns]
    show regNexts _ mems
      (.register r0w "clk" ("rst", .asynchronous) (.ref cw0) v0 ::
        .register r1w "clk" ("rst", .asynchronous) (.ref cw1) v1 ::
          .assign "out" (.ref rW) :: []) envF = _
    have maskEq0 : mask (declaredWidths st r0w) (eval bvals
        (fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
          else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n) e0).toNat =
        (eval bvals
          (fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
            else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n) e0).toNat := by
      rw [wR0]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    have maskEq1 : mask (declaredWidths st r1w) (eval bvals
        (fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
          else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n) e1).toNat =
        (eval bvals
          (fun j n => if j = kv then BitVec.ofNat n (env0 r0w)
            else if j = kv + 1 then BitVec.ofNat n (env0 r1w) else vvals j n) e1).toNat := by
      rw [wR1]
      exact Nat.mod_eq_of_lt (BitVec.isLt _)
    simp [regNexts, evalExpr, hcw0F, hcw1F, hrstF, maskEq0, maskEq1]
  have seqM : SeqBody m.body := by
    rw [mBody, ← preEq]
    intro stq hq
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl (preAssigns stq hq)
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact Or.inr ⟨_, _, _, _, _, rfl⟩
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact Or.inr ⟨_, _, _, _, _, rfl⟩
        · rcases List.mem_cons.mp hq with rfl | hnil
          · exact Or.inl ⟨_, _, rfl⟩
          · cases hnil
  have mem0 : memNexts (declaredWidths st) m.body mems envF = some mems := memNexts_seq seqM
  have scalarSt : ScalarWires st := by
    intro q hq
    rw [stWires] at hq
    apply frame1.scalar
    · apply frame0.scalar
      · intro q2 hq2
        rw [s2bWires] at hq2
        rcases List.mem_cons.mp hq2 with rfl | hq2
        · exact Or.inr ⟨w, rfl⟩
        · rcases List.mem_cons.mp hq2 with rfl | hq2
          · exact Or.inr ⟨w, rfl⟩
          · exact (prepare_shape (bs.zip ids) _ (by
              intro q3 hq3
              rw [show (start (entryCompilerState false cache) declName.toString).state =
                CircuitM.init declName.toString from rfl, init_wires] at hq3
              cases hq3)).1 q2 hq2
    · exact hq
  have wm : weOf m = declaredWidths st := by
    rw [weOf_eq_moduleWidths (by
      intro q hq
      rw [mWires, List.mem_reverse] at hq
      exact scalarSt q hq)]
    exact moduleWidths_finish mWires wiresSt
  have nodupM : (m.wires.map (·.name)).Nodup := by
    rw [mWires, List.map_reverse]
    exact nodup_reverse wiresSt.1
  have allocM : ∀ q ∈ m.wires, Sparkle.IR.NameHints.Allocated q.name := by
    intro q hq
    rw [mWires, List.mem_reverse] at hq
    exact allocSt q hq
  have outNotWire : "out" ∉ m.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    exact not_allocated_out (eq ▸ allocM q hq)
  have smWiresEq : sm.module.wires = st.module.wires := by
    rw [ht, emitAssign_wires, addOutput_state]
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).wires = mo.wires from
      fun _ _ => rfl]
  have wSm : declaredWidths sm rW = w := by
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths
    rw [smWiresEq]
    rw [hrW0]
    exact wR0
  have tyBW : ty.bitWidth = w := by
    rw [hty]
    unfold Tools.ShippingEntrySoundness.leafOutputType
    unfold Tools.ShippingMixedOutputSoundness.declaredWidths at wSm
    cases hf : sm.module.wires.find? (fun q => q.name == rW) with
    | none =>
      rw [hf] at wSm
      simp at wSm
      omega
    | some q =>
      rw [hf] at wSm
      simpa using wSm
  have mOutputs : m.outputs = [{ name := "out", ty := ty }] := by
    have outputsSm : sm.module.outputs = [] := by
      rw [hrec]
      show smR.module.outputs = _
      rw [hsmR, hs4b, hs4a]
      show ((sc1.module.addStmt _).addStmt _).outputs = _
      rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addStmt q).outputs = mo.outputs from
        fun _ _ => rfl,
        show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addStmt q).outputs = mo.outputs from
        fun _ _ => rfl,
        frame1.outputs, frame0.outputs, s2bModule, makeWire_outputs, hs1a, makeWire_outputs,
        (prepare_shape (bs.zip ids) _ (by
          intro q hq'
          rw [show (start (entryCompilerState false cache) declName.toString).state =
            CircuitM.init declName.toString from rfl, init_wires] at hq'
          cases hq')).2]
      rfl
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).outputs = _
    simp only [Module.finalize, (addClockReset_facts st.module).2.2.1]
    rw [ht, emitAssign_outputs, addOutput_state]
    simp [Module.addOutput, outputsSm]
  have wmOut : (Sparkle.IR.Optimize.buildWidthMap m).get? "out" = some w := by
    unfold Sparkle.IR.Optimize.buildWidthMap
    rw [Tools.ShippingPostSoundness.wmFold_notin m.wires _ "out" outNotWire, mOutputs]
    simp [Std.HashMap.get?_insert, tyBW]
  have bodyEq : (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split
    · rfl
    · show m.body.filterMap (Sparkle.IR.ZeroWidth.dzStmt (Sparkle.IR.Optimize.buildWidthMap m))
        = m.body
      apply Tools.ShippingPostSoundness.filterMap_eq_self
      intro stq hst
      rw [mBody] at hst
      rcases List.mem_append.mp hst with hpre | hrest
      · obtain ⟨l, rhs, rfl, htyped⟩ := invC1.typed stq (List.mem_reverse.mp hpre)
        have hpos : 0 < weOf m l := by rw [wm]; exact htyped.positive
        have hg := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpos
        have htym : TypedExpr (weOf m) rhs (weOf m l) := by rw [wm]; exact htyped
        have hwmr : ∀ x ∈ Sparkle.IR.Reorder.refsOf rhs,
            Sparkle.IR.ZeroWidth.exprWidth (Sparkle.IR.Optimize.buildWidthMap m)
              (.ref x) ≠ 0 := by
          intro x hx
          have hpx := htym.refs_positive x hx
          have hgx := Tools.ShippingTypedPostSoundness.widthMap_internal nodupM hpx
          simp only [Sparkle.IR.ZeroWidth.exprWidth, Std.HashMap.getD_eq_getD_getElem?,
            ← Std.HashMap.get?_eq_getElem?, hgx, Option.getD_some]
          omega
        rw [dzStmt_assign _ _ _ hg (by omega),
          Tools.ShippingTypedPostSoundness.dzExpr_typed htym _ hwmr]
      · rcases List.mem_cons.mp hrest with rfl | hrest
        · simp [Sparkle.IR.ZeroWidth.dzStmt, Sparkle.IR.ZeroWidth.dzExpr]
        · rcases List.mem_cons.mp hrest with rfl | hrest
          · simp [Sparkle.IR.ZeroWidth.dzStmt, Sparkle.IR.ZeroWidth.dzExpr]
          · rcases List.mem_cons.mp hrest with rfl | hnil
            · rw [dzStmt_assign _ _ _ wmOut (by omega)]
              simp [Sparkle.IR.ZeroWidth.dzExpr]
            · cases hnil
  have weEq : weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m := by
    unfold Sparkle.IR.ZeroWidth.dropZeroWidthModule
    split
    · rfl
    · exact (weOf_congr_wires rfl).trans (Tools.ShippingPostSoundness.weOf_dropWires m nodupM)
  refine ⟨by rw [wm]; exact wR0, by rw [wm]; exact wR1, bodyEq, weEq, envF, ?_, ?_⟩
  · rw [wm]
    unfold stepModule
    simp [evalFull, nexts, mem0, bind]
  · show (if "out" = "out" then res1 rW else res1 "out") = env0 r0w
    rw [if_pos rfl, hrW0]
    exact resR0


theorem instantiated_input_shift4 {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    (len : ids.length = bs.length) {j : Nat} (hj : j < bs.length) :
    instFVars (ids.map Lean.Expr.fvar).toArray 4 (inputExpr (bs.length + 4) j) =
      .fvar ids[j]! := by
  simp only [Tools.ShippingMixedSourceBridge.inputExpr, instFVars,
    List.size_toArray, List.length_map]
  rw [if_neg (by omega), if_pos (by omega)]
  have eq : ids.length - 1 - (bs.length + 4 - 1 - j - 4) = j := by omega
  rw [eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by omega : j < ids.length)]

theorem instantiated_input_shift5 {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    (len : ids.length = bs.length) {j : Nat} (hj : j < bs.length) :
    instFVars (ids.map Lean.Expr.fvar).toArray 5 (inputExpr (bs.length + 5) j) =
      .fvar ids[j]! := by
  simp only [Tools.ShippingMixedSourceBridge.inputExpr, instFVars,
    List.size_toArray, List.length_map]
  rw [if_neg (by omega), if_pos (by omega)]
  have eq : ids.length - 1 - (bs.length + 5 - 1 - j - 5) = j := by omega
  rw [eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by omega : j < ids.length)]

theorem instantiated_input_shift6 {bs : List (Name × MixedGateBinder)} {ids : List FVarId}
    (len : ids.length = bs.length) {j : Nat} (hj : j < bs.length) :
    instFVars (ids.map Lean.Expr.fvar).toArray 6 (inputExpr (bs.length + 6) j) =
      .fvar ids[j]! := by
  simp only [Tools.ShippingMixedSourceBridge.inputExpr, instFVars,
    List.size_toArray, List.length_map]
  rw [if_neg (by omega), if_pos (by omega)]
  have eq : ids.length - 1 - (bs.length + 6 - 1 - j - 6) = j := by omega
  rw [eq]
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem (by omega : j < ids.length)]

theorem instFVars_read2E (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr) (w : Nat)
    (x : Lean.Expr) :
    instFVars xs d (read2E dom w x) =
      read2E (instFVars xs d dom) w (instFVars xs d x) := rfl

theorem synthesizeFromConst_cdo2_sound {logProf declName ci bs body m d} {isInst : Lean.Expr → Bool}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci isInst = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci isInst) (m, d)) :
    Cdo2Preserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_cdo2_sound run

theorem synthesizeCombinationalCore_cdo2_sound {declName : Name}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        (∀ isInst, mixedCertifiedShape? false [] ci isInst = some (bs, body)) →
        Cdo2Preserves declName bs body m := by
  obtain ⟨logProf, envR, ci, w1, w2, w3, w4, w5, w6, get, henv, run⟩ :=
    synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape =>
    synthesizeFromConst_cdo2_sound old (shape _) (Tools.ShippingEntrySoundness.entry_kept (shape _) run).mreturns⟩

/-- Position plumbing for the two-slot circuit-do root (first slot returned). -/
theorem cdo2_source {declName : Name} {bs : List (Name × MixedGateBinder)}
    {body : Lean.Expr} {m : Sparkle.IR.AST.Module} {nmX nmY : Name} {dpos : Nat}
    {w v0 v1 kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e0 e1 : Term (.bits w)}
    (source : Cdo2Preserves declName bs body m)
    (hbody : body = cdo2E nmX nmY
      (inputExpr bs.length dpos) (inputExpr (bs.length + 1) dpos)
      (inputExpr (bs.length + 2) dpos) (inputExpr (bs.length + 3) dpos)
      (inputExpr (bs.length + 4) dpos) (inputExpr (bs.length + 5) dpos)
      (inputExpr (bs.length + 6) dpos) w v0 v1
      (read2E (inputExpr (bs.length + 6) dpos) w (.bvar 4))
      (quote (inputExpr (bs.length + 4) dpos)
        (fun j => inputExpr (bs.length + 4) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 2)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 0)
          else inputExpr (bs.length + 4) (vpos j)) e0)
      (quote (inputExpr (bs.length + 5) dpos)
        (fun j => inputExpr (bs.length + 5) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 3)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 1)
          else inputExpr (bs.length + 5) (vpos j)) e1))
    (hdp : dpos < bs.length)
    (hself0 : vw kv = w) (hself1 : vw (kv + 1) = w)
    (he0 : e0.WF kb (kv + 2) vw) (he1 : e1.WF kb (kv + 2) vw)
    (hv0 : v0 < 2 ^ w) (hv1 : v1 < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r0 r1 : String), r0 ≠ r1 ∧
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r0 < 2 ^ w → env0 r1 < 2 ^ w →
      weOf m r0 = w ∧ weOf m r1 = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF,
            [(r0, (eval (fun j => bools (bpos j))
              (fun j n => if j = kv then BitVec.ofNat n (env0 r0)
                else if j = kv + 1 then BitVec.ofNat n (env0 r1)
                else bits (vpos j) n) e0).toNat),
             (r1, (eval (fun j => bools (bpos j))
              (fun j n => if j = kv then BitVec.ofNat n (env0 r0)
                else if j = kv + 1 then BitVec.ofNat n (env0 r1)
                else bits (vpos j) n) e1).toNat)], mems) ∧
        envF "out" = env0 r0 := by
  obtain ⟨ids, nd, len, cache, H⟩ := source
  have qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      cdo2E nmX nmY (.fvar ids[dpos]!) (.fvar ids[dpos]!) (.fvar ids[dpos]!)
        (.fvar ids[dpos]!) (.fvar ids[dpos]!) (.fvar ids[dpos]!) (.fvar ids[dpos]!) w v0 v1
        (read2E (.fvar ids[dpos]!) w (.bvar 4))
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => if j = kv then read2E (.fvar ids[dpos]!) w (.bvar 2)
            else if j = kv + 1 then read2E (.fvar ids[dpos]!) w (.bvar 0)
            else .fvar ids[vpos j]!) e0)
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => if j = kv then read2E (.fvar ids[dpos]!) w (.bvar 3)
            else if j = kv + 1 then read2E (.fvar ids[dpos]!) w (.bvar 1)
            else .fvar ids[vpos j]!) e1) := by
    rw [hbody, instFVars_cdo2E, instantiated_input len hdp, instantiated_input_shift len hdp,
      instantiated_input_shift2 len hdp, instantiated_input_shift3 len hdp,
      instantiated_input_shift4 len hdp, instantiated_input_shift5 len hdp,
      instantiated_input_shift6 len hdp]
    congr 1
    · rw [instFVars_read2E, instantiated_input_shift6 len hdp]
      rfl
    · rw [show (Lean.Expr.fvar ids[dpos]!) =
        instFVars (ids.map Lean.Expr.fvar).toArray 4 (inputExpr (bs.length + 4) dpos) from
        (instantiated_input_shift4 len hdp).symm]
      rw [instFVars_quote]
      apply quote_congr _ _ e0 he0
      · intro j hj
        exact instantiated_input_shift4 len
          (List.getElem_of_getElem? (hb j hj).choose_spec).choose
      · intro j hj
        by_cases hkv : j = kv
        · subst hkv
          simp only [if_pos rfl, if_true, Nat.zero_add]
          rw [instFVars_read2E, instantiated_input_shift4 len hdp]
          rfl
        · by_cases hkv1 : j = kv + 1
          · subst hkv1
            simp only [if_neg (by omega : ¬(kv + 1 = kv)), if_pos rfl, if_true]
            rw [instFVars_read2E, instantiated_input_shift4 len hdp]
            rfl
          · have hjlt : j < kv := by omega
            simp only [if_neg hkv, if_neg hkv1]
            exact instantiated_input_shift4 len
              (List.getElem_of_getElem? (hvp j hjlt).choose_spec).choose
    · rw [show (Lean.Expr.fvar ids[dpos]!) =
        instFVars (ids.map Lean.Expr.fvar).toArray 5 (inputExpr (bs.length + 5) dpos) from
        (instantiated_input_shift5 len hdp).symm]
      rw [instFVars_quote]
      apply quote_congr _ _ e1 he1
      · intro j hj
        exact instantiated_input_shift5 len
          (List.getElem_of_getElem? (hb j hj).choose_spec).choose
      · intro j hj
        by_cases hkv : j = kv
        · subst hkv
          simp only [if_pos rfl, if_true]
          rw [instFVars_read2E, instantiated_input_shift5 len hdp]
          rfl
        · by_cases hkv1 : j = kv + 1
          · subst hkv1
            simp only [if_neg (by omega : ¬(kv + 1 = kv)), if_pos rfl, if_true]
            rw [instFVars_read2E, instantiated_input_shift5 len hdp]
            rfl
          · have hjlt : j < kv := by omega
            simp only [if_neg hkv, if_neg hkv1]
            exact instantiated_input_shift5 len
              (List.getElem_of_getElem? (hvp j hjlt).choose_spec).choose
  obtain ⟨r0, r1, hne, H⟩ := H nmX nmY (.fvar ids[dpos]!) (.fvar ids[dpos]!)
    (.fvar ids[dpos]!) kb kv vw (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) e0 e1
    (by rfl) (cdo2ConeToLoop_fvar 2 0 4 0 ids[dpos]!) (cdo2ConeToLoop_fvar 3 1 5 0 ids[dpos]!)
    hself0 hself1 he0 he1 hv0 hv1 qeq
  refine ⟨ids, nd, len, cache, r0, r1, hne, ?_⟩
  intro bools bits env0 mems values hrst0 h0b h1b
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  apply H (boolValues ids bools) (bitValues ids bits) env0 mems
    (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) values _ _ hrst0 h0b h1b
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bool_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [boolValues, index_fresh ids nd (bpos j) (by omega)] using lookup
  · intro j hj
    obtain ⟨name, pos⟩ := hvp j hj
    have bound := (List.getElem_of_getElem? pos).choose
    have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [bitValues, index_fresh ids nd (vpos j) (by omega)] using lookup

/-- General two-slot circuit-do endpoint at the real core entry. -/
theorem cdo2_step_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {nmX nmY : Name} {dpos : Nat}
    {w v0 v1 kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e0 e1 : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, cdo2E nmX nmY
      (inputExpr bs.length dpos) (inputExpr (bs.length + 1) dpos)
      (inputExpr (bs.length + 2) dpos) (inputExpr (bs.length + 3) dpos)
      (inputExpr (bs.length + 4) dpos) (inputExpr (bs.length + 5) dpos)
      (inputExpr (bs.length + 6) dpos) w v0 v1
      (read2E (inputExpr (bs.length + 6) dpos) w (.bvar 4))
      (quote (inputExpr (bs.length + 4) dpos)
        (fun j => inputExpr (bs.length + 4) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 2)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 0)
          else inputExpr (bs.length + 4) (vpos j)) e0)
      (quote (inputExpr (bs.length + 5) dpos)
        (fun j => inputExpr (bs.length + 5) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 3)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 1)
          else inputExpr (bs.length + 5) (vpos j)) e1)))
    (hdp : dpos < bs.length)
    (hself0 : vw kv = w) (hself1 : vw (kv + 1) = w)
    (he0 : e0.WF kb (kv + 2) vw) (he1 : e1.WF kb (kv + 2) vw)
    (hv0 : v0 < 2 ^ w) (hv1 : v1 < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r0 r1 : String), r0 ≠ r1 ∧
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      env0 "rst" = 0 → env0 r0 < 2 ^ w → env0 r1 < 2 ^ w →
      weOf m r0 = w ∧ weOf m r1 = w ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule m).body = m.body ∧
      weOf (Sparkle.IR.ZeroWidth.dropZeroWidthModule m) = weOf m ∧
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF,
            [(r0, (eval (fun j => bools (bpos j))
              (fun j n => if j = kv then BitVec.ofNat n (env0 r0)
                else if j = kv + 1 then BitVec.ofNat n (env0 r1)
                else bits (vpos j) n) e0).toNat),
             (r1, (eval (fun j => bools (bpos j))
              (fun j n => if j = kv then BitVec.ofNat n (env0 r0)
                else if j = kv + 1 then BitVec.ofNat n (env0 r1)
                else bits (vpos j) n) e1).toNat)], mems) ∧
        envF "out" = env0 r0 := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_cdo2_sound hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have mixedGate := cdo2_term_gate (d := d)
    (by rw [definition]; exact peel) hdp rfl hself0 hself1 hv0 hv1 he0 he1 hb hvp
  exact cdo2_source (source bs _ oldGate mixedGate) rfl hdp hself0 hself1 he0 he1 hv0 hv1
    hb hvp

/-- Two-register trace iteration with state-reading updates: `out` observes
register 0, both registers step by functions of the wall-clock cycle and the
current state pair, and the invariant `P` (the width bound) is carried on
both states. -/
theorem trace_of_cycles2_inv {we : WEnv} {body : List Stmt} {r0 r1 : String} {mems : MEnv}
    {seed : Nat → (String → Nat) → Env} {F0 F1 : Nat → Nat → Nat → Nat} {P : Nat → Prop}
    (hne : r0 ≠ r1)
    (step : ∀ t stv, P (stv r0) → P (stv r1) → ∃ envF,
      stepModule we body (seed t stv) mems =
        some (envF, [(r0, F0 t (stv r0) (stv r1)), (r1, F1 t (stv r0) (stv r1))], mems) ∧
      envF "out" = stv r0)
    (P0step : ∀ t s0 s1, P s0 → P s1 → P (F0 t s0 s1))
    (P1step : ∀ t s0 s1, P s0 → P s1 → P (F1 t s0 s1)) :
    ∀ (k : Nat) (st0 : String → Nat) (S0 S1 : Nat → Nat),
      P (st0 r0) → P (st0 r1) → S0 0 = st0 r0 → S1 0 = st0 r1 →
      (∀ j, j + 1 ≤ k → S0 (j + 1) = F0 (k - 1 - j) (S0 j) (S1 j)) →
      (∀ j, j + 1 ≤ k → S1 (j + 1) = F1 (k - 1 - j) (S0 j) (S1 j)) →
      ∃ envs, runModule we body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S0 j
  | 0, st0, S0, S1, _, _, hS00, hS10, hS0s, hS1s =>
    ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, st0, S0, S1, P0, P1, hS00, hS10, hS0s, hS1s => by
    obtain ⟨envF, hstep, hout⟩ := step k st0 P0 P1
    have hnext0 : applyNexts st0 [(r0, F0 k (st0 r0) (st0 r1)),
        (r1, F1 k (st0 r0) (st0 r1))] r0 = F0 k (st0 r0) (st0 r1) := by
      simp [applyNexts]
    have hnext1 : applyNexts st0 [(r0, F0 k (st0 r0) (st0 r1)),
        (r1, F1 k (st0 r0) (st0 r1))] r1 = F1 k (st0 r0) (st0 r1) := by
      have hne' : (r0 == r1) = false := by
        cases h : r0 == r1
        · rfl
        · exact absurd (eq_of_beq h) hne
      simp [applyNexts, hne']
    obtain ⟨rest, hrun, hlen, hobs⟩ := trace_of_cycles2_inv hne step P0step P1step k
      (applyNexts st0 [(r0, F0 k (st0 r0) (st0 r1)), (r1, F1 k (st0 r0) (st0 r1))])
      (fun j => S0 (j + 1)) (fun j => S1 (j + 1))
      (by rw [hnext0]; exact P0step k _ _ P0 P1)
      (by rw [hnext1]; exact P1step k _ _ P0 P1)
      (by
        show S0 (0 + 1) = _
        rw [hnext0, hS0s 0 (by omega), hS00, hS10]
        simp)
      (by
        show S1 (0 + 1) = _
        rw [hnext1, hS1s 0 (by omega), hS00, hS10]
        simp)
      (by
        intro j hj
        show S0 (j + 1 + 1) = _
        rw [hS0s (j + 1) (by omega)]
        have hidx : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
        rw [hidx])
      (by
        intro j hj
        show S1 (j + 1 + 1) = _
        rw [hS1s (j + 1) (by omega)]
        have hidx : k + 1 - 1 - (j + 1) = k - 1 - j := by omega
        rw [hidx])
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj
      cases j with
      | zero => rw [hS00]; simpa using hout
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget]
        exact hobs i hi

/-- Packaged two-slot circuit-do trace at the real core entry: the compiled
`runModule` trace observes the first register's stream while both registers
follow their cones at the current state pair. -/
theorem cdo2_run_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)} {nmX nmY : Name} {dpos : Nat}
    {w v0 v1 kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat} {e0 e1 : Term (.bits w)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, cdo2E nmX nmY
      (inputExpr bs.length dpos) (inputExpr (bs.length + 1) dpos)
      (inputExpr (bs.length + 2) dpos) (inputExpr (bs.length + 3) dpos)
      (inputExpr (bs.length + 4) dpos) (inputExpr (bs.length + 5) dpos)
      (inputExpr (bs.length + 6) dpos) w v0 v1
      (read2E (inputExpr (bs.length + 6) dpos) w (.bvar 4))
      (quote (inputExpr (bs.length + 4) dpos)
        (fun j => inputExpr (bs.length + 4) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 2)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 4) dpos) w (.bvar 0)
          else inputExpr (bs.length + 4) (vpos j)) e0)
      (quote (inputExpr (bs.length + 5) dpos)
        (fun j => inputExpr (bs.length + 5) (bpos j))
        (fun j => if j = kv then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 3)
          else if j = kv + 1 then read2E (inputExpr (bs.length + 5) dpos) w (.bvar 1)
          else inputExpr (bs.length + 5) (vpos j)) e1)))
    (hdp : dpos < bs.length)
    (hself0 : vw kv = w) (hself1 : vw (kv + 1) = w)
    (he0 : e0.WF kb (kv + 2) vw) (he1 : e1.WF kb (kv + 2) vw)
    (hv0 : v0 < 2 ^ w) (hv1 : v1 < 2 ^ w)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (r0 r1 : String), r0 ≠ r1 ∧
      ∀ (bools : Nat → Nat → Bool) (bits : Nat → (j : Nat) → (n : Nat) → BitVec n)
        (mems : MEnv) (k : Nat) (seed : Nat → (String → Nat) → Env)
        (st0 : String → Nat) (S0 S1 : Nat → Nat),
      (∀ t stv, SourceInputs declName bs ids cache (bools (k - 1 - t)) (bits (k - 1 - t))
          (seed t stv) ∧ seed t stv "rst" = 0 ∧
          seed t stv r0 = stv r0 ∧ seed t stv r1 = stv r1) →
      st0 r0 < 2 ^ w → st0 r1 < 2 ^ w →
      S0 0 = st0 r0 → S1 0 = st0 r1 →
      (∀ j, j + 1 ≤ k → S0 (j + 1) = (eval (fun i => bools j (bpos i))
        (fun i n => if i = kv then BitVec.ofNat n (S0 j)
          else if i = kv + 1 then BitVec.ofNat n (S1 j)
          else bits j (vpos i) n) e0).toNat) →
      (∀ j, j + 1 ≤ k → S1 (j + 1) = (eval (fun i => bools j (bpos i))
        (fun i n => if i = kv then BitVec.ofNat n (S0 j)
          else if i = kv + 1 then BitVec.ofNat n (S1 j)
          else bits j (vpos i) n) e1).toNat) →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems = some envs ∧ envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S0 j := by
  obtain ⟨ids, nd, len, cache, r0, r1, hne, H⟩ :=
    cdo2_step_of_env hr env old peel hdp hself0 hself1 he0 he1 hv0 hv1 hb hvp
  refine ⟨ids, nd, len, cache, r0, r1, hne, ?_⟩
  intro bools bits mems k seed st0 S0 S1 hseed hst0 hst1 hS00 hS10 hS0s hS1s
  apply trace_of_cycles2_inv (P := fun s => s < 2 ^ w) hne
    (F0 := fun t s0 s1 => (eval (fun i => bools (k - 1 - t) (bpos i))
      (fun i n => if i = kv then BitVec.ofNat n s0
        else if i = kv + 1 then BitVec.ofNat n s1
        else bits (k - 1 - t) (vpos i) n) e0).toNat)
    (F1 := fun t s0 s1 => (eval (fun i => bools (k - 1 - t) (bpos i))
      (fun i n => if i = kv then BitVec.ofNat n s0
        else if i = kv + 1 then BitVec.ofNat n s1
        else bits (k - 1 - t) (vpos i) n) e1).toNat)
    ?_ ?_ ?_ k st0 S0 S1 hst0 hst1 hS00 hS10 ?_ ?_
  · intro t stv hP0 hP1
    obtain ⟨hsrc, hrst, hread0, hread1⟩ := hseed t stv
    obtain ⟨-, -, -, -, envF, hstep, hout⟩ :=
      H (bools (k - 1 - t)) (bits (k - 1 - t)) (seed t stv) mems hsrc hrst
        (by rw [hread0]; exact hP0) (by rw [hread1]; exact hP1)
    refine ⟨envF, ?_, by rw [hout, hread0]⟩
    rw [hread0, hread1] at hstep
    exact hstep
  · intro t s0 s1 _ _
    exact BitVec.isLt _
  · intro t s0 s1 _ _
    exact BitVec.isLt _
  · intro j hj
    rw [hS0s j hj]
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    rw [hidx]
  · intro j hj
    rw [hS1s j hj]
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    rw [hidx]

/-- The reduced two-slot `circuit do` state: `Signal.loop` over the packed
pair of registers, each cone reading both slots through the handle
projections. -/
def loopPair {D : Sparkle.Core.Domain.DomainConfig} {w : Nat} (i0 i1 : BitVec w)
    (cone0 cone1 : Sparkle.Core.Signal.Signal D (BitVec w) →
      Sparkle.Core.Signal.Signal D (BitVec w) →
      Sparkle.Core.Signal.Signal D (BitVec w)) :
    Sparkle.Core.Signal.Signal D (BitVec w × (BitVec w × Unit)) :=
  Sparkle.Core.Signal.Signal.loop (fun live =>
    Sparkle.Core.Signal.bundle2
      (Sparkle.Core.Signal.Signal.register i0
        (cone0 (Sparkle.Core.Signal.Signal.map Prod.fst live)
          (Sparkle.Core.Signal.Signal.map Prod.fst
            (Sparkle.Core.Signal.Signal.map Prod.snd live))))
      (Sparkle.Core.Signal.bundle2
        (Sparkle.Core.Signal.Signal.register i1
          (cone1 (Sparkle.Core.Signal.Signal.map Prod.fst live)
            (Sparkle.Core.Signal.Signal.map Prod.fst
              (Sparkle.Core.Signal.Signal.map Prod.snd live))))
        (Sparkle.Core.Signal.Signal.pure ())))

/-- The two projected register streams of the reduced two-slot state follow
the mutual recurrence: both start at their declared initial values, and each
steps by its cone applied to the pair of live streams. -/
theorem loopPair_val {D : Sparkle.Core.Domain.DomainConfig} {w : Nat} (i0 i1 : BitVec w)
    (cone0 cone1 : Sparkle.Core.Signal.Signal D (BitVec w) →
      Sparkle.Core.Signal.Signal D (BitVec w) →
      Sparkle.Core.Signal.Signal D (BitVec w))
    (hcone0 : ∀ (a a' b b' : Sparkle.Core.Signal.Signal D (BitVec w)) (t : Nat),
      a.val t = a'.val t → b.val t = b'.val t →
      (cone0 a b).val t = (cone0 a' b').val t)
    (hcone1 : ∀ (a a' b b' : Sparkle.Core.Signal.Signal D (BitVec w)) (t : Nat),
      a.val t = a'.val t → b.val t = b'.val t →
      (cone1 a b).val t = (cone1 a' b').val t) :
    ((Sparkle.Core.Signal.Signal.map Prod.fst (loopPair i0 i1 cone0 cone1)).val 0 = i0) ∧
    ((Sparkle.Core.Signal.Signal.map Prod.fst
      (Sparkle.Core.Signal.Signal.map Prod.snd (loopPair i0 i1 cone0 cone1))).val 0 = i1) ∧
    (∀ t, (Sparkle.Core.Signal.Signal.map Prod.fst (loopPair i0 i1 cone0 cone1)).val (t + 1) =
      (cone0 (Sparkle.Core.Signal.Signal.map Prod.fst (loopPair i0 i1 cone0 cone1))
        (Sparkle.Core.Signal.Signal.map Prod.fst
          (Sparkle.Core.Signal.Signal.map Prod.snd (loopPair i0 i1 cone0 cone1)))).val t) ∧
    (∀ t, (Sparkle.Core.Signal.Signal.map Prod.fst
        (Sparkle.Core.Signal.Signal.map Prod.snd (loopPair i0 i1 cone0 cone1))).val (t + 1) =
      (cone1 (Sparkle.Core.Signal.Signal.map Prod.fst (loopPair i0 i1 cone0 cone1))
        (Sparkle.Core.Signal.Signal.map Prod.fst
          (Sparkle.Core.Signal.Signal.map Prod.snd (loopPair i0 i1 cone0 cone1)))).val t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Prod.fst (Sparkle.Core.Signal.Signal.loopGo _ 0) = i0
    rw [Sparkle.Core.Signal.Signal.loopGo_eq]
    rfl
  · show Prod.fst (Prod.snd (Sparkle.Core.Signal.Signal.loopGo _ 0)) = i1
    rw [Sparkle.Core.Signal.Signal.loopGo_eq]
    rfl
  · intro t
    show Prod.fst (Sparkle.Core.Signal.Signal.loopGo _ (t + 1)) = _
    rw [Sparkle.Core.Signal.Signal.loopGo_eq]
    show (cone0
      (Sparkle.Core.Signal.Signal.map Prod.fst
        ⟨fun i => if i < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ i else default⟩)
      (Sparkle.Core.Signal.Signal.map Prod.fst (Sparkle.Core.Signal.Signal.map Prod.snd
        ⟨fun i => if i < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ i else default⟩))).val t
      = _
    apply hcone0
    · show Prod.fst (if t < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ t else default) = _
      rw [if_pos (by omega)]
      rfl
    · show Prod.fst (Prod.snd
        (if t < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ t else default)) = _
      rw [if_pos (by omega)]
      rfl
  · intro t
    show Prod.fst (Prod.snd (Sparkle.Core.Signal.Signal.loopGo _ (t + 1))) = _
    rw [Sparkle.Core.Signal.Signal.loopGo_eq]
    show (cone1
      (Sparkle.Core.Signal.Signal.map Prod.fst
        ⟨fun i => if i < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ i else default⟩)
      (Sparkle.Core.Signal.Signal.map Prod.fst (Sparkle.Core.Signal.Signal.map Prod.snd
        ⟨fun i => if i < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ i else default⟩))).val t
      = _
    apply hcone1
    · show Prod.fst (if t < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ t else default) = _
      rw [if_pos (by omega)]
      rfl
    · show Prod.fst (Prod.snd
        (if t < t + 1 then Sparkle.Core.Signal.Signal.loopGo _ t else default)) = _
      rw [if_pos (by omega)]
      rfl

end Tools.ShippingRegisterSoundness
