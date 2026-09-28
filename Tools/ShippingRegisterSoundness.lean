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
    mixedCertifiedShape? false [] (.defnInfo d) = some (bs, registerE dom w v
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) e)) := by
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

/-! ## Real-entry connection -/

theorem synthesizeFromConst_register_sound {logProf declName ci bs body m d}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci) (m, d)) :
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
        mixedCertifiedShape? false [] ci = some (bs, body) →
        RegisterPreserves declName bs body m := by
  obtain ⟨logProf, ci, w1, w2, w3, get, run⟩ := synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape =>
    synthesizeFromConst_register_sound old shape run.mreturns⟩

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

/-! ## Trace iteration -/

/-- Iterating the per-cycle property along `runModule`: cycle `j` (wall-clock,
oldest first) observes the register state, which follows the recurrence
`st0 r, F (k-1), F (k-2), …` (`runModule`'s seed index counts down). -/
theorem trace_of_cycles {we : WEnv} {body : List Stmt} {r : String} {mems : MEnv}
    {seed : Nat → (String → Nat) → Env} {F : Nat → Nat}
    (step : ∀ t stv, ∃ envF,
      stepModule we body (seed t stv) mems = some (envF, [(r, F t)], mems) ∧
      envF "out" = stv r) :
    ∀ (k : Nat) (st0 : String → Nat), ∃ envs,
      runModule we body seed k st0 mems = some envs ∧ envs.length = k ∧
      ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
        (if j = 0 then st0 r else F (k - j))
  | 0, st0 => ⟨[], rfl, rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | k + 1, st0 => by
    obtain ⟨envF, hstep, hout⟩ := step k st0
    obtain ⟨rest, hrun, hlen, hobs⟩ := trace_of_cycles step k (applyNexts st0 [(r, F k)])
    refine ⟨envF :: rest, ?_, by simp [hlen], ?_⟩
    · unfold runModule
      simp [hstep, bind, hrun]
    · intro j hj
      cases j with
      | zero => simpa using hout
      | succ i =>
        have hi : i < rest.length := by simpa using hj
        have hrest := hobs i hi
        have hget : ((envF :: rest)[i + 1]'hj) = rest[i]'hi := by simp
        rw [hget, hrest]
        by_cases h0 : i = 0
        · subst h0
          simp [applyNexts]
        · have hik : i < k := by omega
          simp only [h0, if_false, Nat.succ_ne_zero]
          congr 1
          omega

end Tools.ShippingRegisterSoundness
