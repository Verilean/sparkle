import Tools.ShippingRegisterSoundness
import Tools.ShippingMemorySoundness

/-! # S5-2: the canonical memory at the real core entry

The canonical `Signal.memory wa wd wen ra` root (all four operands input
binders) now has a total lowering (`translateMemoryUncachedWith`) and a
gate disjunct (`unifiedMemoryRoot`). This module proves the compiled
module IS the canonical memory body of the semantics layer: the four
operand translations are pure input reads (they change no state), the
emitter appends exactly the `.memory` statement and the `rdata` wire,
and the leaf emitter closes with `out := rdata` — so
`Tools.ShippingMemorySoundness.memBody` describes the real module and
its trace theorems apply, premise-free, at the entry.

Scope: the raw synthesized module of `synthesizeCombinationalCore`; the
sequential post-processing passes for memory bodies are separate work. -/
namespace Tools.ShippingMemoryEntrySoundness
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Builder Sparkle.IR.Semantics
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingUnifiedCache Tools.ShippingUnifiedInvariant
open Tools.ShippingUnifiedEntrySoundness
open Tools.ShippingUnifiedRecursion Tools.ShippingUnifiedProtection
open Tools.ShippingCompareLoweringSoundness (ScalarWidthsAgree)
open Tools.ShippingMixedBinarySoundness (ScalarWires)
open Tools.ShippingTranslationOrder
open Tools.ShippingRegisterSoundness (SeqBody)
open Tools.ShippingMemorySoundness (evalPayload_ref)
open Tools.ShippingTranslateSoundness hiding Inv Spec
open Tools.ShippingMixedOutputSoundness (PortInputs declaredWidths declaredWidths_agree)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMixedInputSoundness (empty_layout)
open Tools.ShippingMixedInvariant (Separate translateStep_fvar_returns)
open Tools.ShippingEntrySoundness
open Tools.ShippingBoolSourceSoundness
open Tools.ShippingRegisterSoundness (not_allocated_out prepare_const
  admissible_zero prepare_wires_allocated init_wires)
open Tools.ShippingMuxTypeSoundness (bitVecE canonicalNatLitValue?_natE)
open Tools.ShippingUnifiedExecutionSoundness
open Tools.ShippingMemorySoundness (memBody)

/-! ## The quoted root form -/

/-- `Signal.memory wa wd wen ra`, exactly as the library call elaborates
over a polymorphic domain at literal widths. -/
def memoryE (dom : Lean.Expr) (aw dw : Nat) (wa wd wen ra : Lean.Expr) : Lean.Expr :=
  mkApp7 (.const ``Sparkle.Core.Signal.Signal.memory []) dom (natE aw) (natE dw)
    wa wd wen ra

theorem canonicalMemory?_memoryE {dom wa wd wen ra : Lean.Expr} {aw dw : Nat}
    (hdom : (dom.isFVar || dom.isBVar) = true) (haw : 0 < aw) (hdw : 0 < dw) :
    canonicalMemory? (memoryE dom aw dw wa wd wen ra) = some (aw, dw) := by
  simp only [memoryE, mkApp7, mkApp6, mkApp5, mkApp4, mkApp3, mkApp2, mkAppB, mkApp,
    canonicalMemory?, hdom, if_true, canonicalNatLitValue?_natE]
  simp [haw, hdw]

theorem instFVars_memoryE (xs : Array Lean.Expr) (d : Nat) (dom : Lean.Expr)
    (aw dw : Nat) (wa wd wen ra : Lean.Expr) :
    instFVars xs d (memoryE dom aw dw wa wd wen ra) =
      memoryE (instFVars xs d dom) aw dw (instFVars xs d wa) (instFVars xs d wd)
        (instFVars xs d wen) (instFVars xs d ra) := rfl

/-! ## Gate acceptance -/

theorem mixedGateBVar?_pos {bs : List (Name × MixedGateBinder)} {pos : Nat}
    {name : Name} {k : MixedGateBinder} (h : bs[pos]? = some (name, k)) :
    mixedGateBVar? (bs.map Prod.snd).toArray (bs.length - 1 - pos) = some k := by
  have hlt : pos < bs.length := by
    rcases Nat.lt_or_ge pos bs.length with hl | hg
    · exact hl
    · rw [List.getElem?_eq_none hg] at h
      cases h
  unfold mixedGateBVar?
  have hsize : (bs.map Prod.snd).toArray.size = bs.length := by
    simp
  rw [if_pos (by omega)]
  have hidx : (bs.map Prod.snd).toArray.size - 1 - (bs.length - 1 - pos) = pos := by
    omega
  rw [hidx]
  rw [List.getElem?_toArray, List.getElem?_map, h]
  rfl

theorem unifiedMemoryRoot_memoryE {kinds : Array MixedGateBinder} {dom : Lean.Expr}
    {aw dw : Nat} {wa wd wen ra : Lean.Expr}
    (hdom : (dom.isFVar || dom.isBVar) = true) (haw : 0 < aw) (hdw : 0 < dw)
    (hwa : unifiedGateBitsBody kinds aw wa = true)
    (hwd : unifiedGateBitsBody kinds dw wd = true)
    (hwen : unifiedGateBoolBody kinds wen = true)
    (hra : unifiedGateBitsBody kinds aw ra = true) :
    unifiedMemoryRoot kinds (memoryE dom aw dw wa wd wen ra) = true := by
  show ((dom.isFVar || dom.isBVar) &&
    (match canonicalNatLitValue? (natE aw), canonicalNatLitValue? (natE dw) with
     | some aw', some dw' =>
       0 < aw' && 0 < dw' &&
       unifiedGateBitsBody kinds aw' wa && unifiedGateBitsBody kinds dw' wd &&
       unifiedGateBoolBody kinds wen && unifiedGateBitsBody kinds aw' ra
     | _, _ => false)) = true
  rw [hdom, canonicalNatLitValue?_natE, canonicalNatLitValue?_natE]
  simp [haw, hdw, hwa, hwd, hwen, hra]

/-- Once the real declaration has been peeled to a memory root over input
binders, the shipping gate accepts it. -/
theorem memory_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {aw dw : Nat} {wapos wdpos wenpos rapos : Nat}
    (peel : mixedGatePeel d.value = some (bs, memoryE dom aw dw
      (inputExpr bs.length wapos) (inputExpr bs.length wdpos)
      (inputExpr bs.length wenpos) (inputExpr bs.length rapos)))
    (hdom : (dom.isFVar || dom.isBVar) = true) (haw : 0 < aw) (hdw : 0 < dw)
    (hwa : ∃ name, bs[wapos]? = some (name, .bits aw))
    (hwd : ∃ name, bs[wdpos]? = some (name, .bits dw))
    (hwen : ∃ name, bs[wenpos]? = some (name, .bool))
    (hra : ∃ name, bs[rapos]? = some (name, .bits aw)) :
    mixedCertifiedShape? false [] (.defnInfo d) = some (bs, memoryE dom aw dw
      (inputExpr bs.length wapos) (inputExpr bs.length wdpos)
      (inputExpr bs.length wenpos) (inputExpr bs.length rapos)) := by
  have root := unifiedMemoryRoot_memoryE (kinds := (bs.map Prod.snd).toArray) hdom haw hdw
    (hwa.elim fun name pos => input_bits_accepted pos)
    (hwd.elim fun name pos => input_bits_accepted pos)
    (hwen.elim fun name pos => input_bool_accepted pos)
    (hra.elim fun name pos => input_bits_accepted pos)
  simp only [mixedCertifiedShape?, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, Bool.or_true, if_true]
  rfl

/-! ## The memory emitter, lifted -/

theorem emitMemoryC_spec (hint : String) (aw dw : Nat) (clk : String)
    (wa wd wen ra : Sparkle.IR.AST.Expr) (named : Bool) (s : CircuitState) :
    (CircuitM.emitMemory hint aw dw clk wa wd wen ra named s).1 =
      (CircuitM.freshName (CircuitM.sanitizeName s!"{hint}_rdata") named
        (CircuitM.freshName (CircuitM.sanitizeName hint) named s).2).1 ∧
    (CircuitM.emitMemory hint aw dw clk wa wd wen ra named s).2 =
      { (CircuitM.freshName (CircuitM.sanitizeName s!"{hint}_rdata") named
          (CircuitM.freshName (CircuitM.sanitizeName hint) named s).2).2 with
        module := ((CircuitM.freshName (CircuitM.sanitizeName s!"{hint}_rdata") named
            (CircuitM.freshName (CircuitM.sanitizeName hint) named s).2).2.module.addWire
          { name := (CircuitM.freshName (CircuitM.sanitizeName s!"{hint}_rdata") named
              (CircuitM.freshName (CircuitM.sanitizeName hint) named s).2).1,
            ty := .bitVector dw }).addStmt
          (.memory (CircuitM.freshName (CircuitM.sanitizeName hint) named s).1
            aw dw clk wa wd wen ra
            (CircuitM.freshName (CircuitM.sanitizeName s!"{hint}_rdata") named
              (CircuitM.freshName (CircuitM.sanitizeName hint) named s).2).1) } := by
  constructor <;> rfl

/-- The compiler's `emitMemory` is the builder's; the width-cache write
does not touch the builder state. -/
theorem emitMemory_returns {hint : String} {aw dw : Nat} {clk : String}
    {wa wd wen ra : Sparkle.IR.AST.Expr} {named : Bool}
    {ctx : CompilerState} {s s' : CircuitState} {w : String}
    (h : Returns (CompilerM.emitMemory hint aw dw clk wa wd wen ra (named := named))
      ctx s w s') :
    w = (CircuitM.emitMemory hint aw dw clk wa wd wen ra named s).1 ∧
    s' = (CircuitM.emitMemory hint aw dw clk wa wd wen ra named s).2 := by
  unfold CompilerM.emitMemory at h
  obtain ⟨cs, s1, hget, k1⟩ := Returns.bind h
  obtain ⟨hcs, hs1⟩ := Returns.get hget
  subst hcs hs1
  split at k1
  rename_i name cs' hmk
  obtain ⟨u, s2, hset, k2⟩ := Returns.bind k1
  have hs2 : s2 = cs' := Returns.set hset
  have goal : w = name ∧ s' = s2 := by
    obtain ⟨u2, s3, hlift, k3⟩ := Returns.bind k2
    have h3 : s3 = s2 := Returns.liftMetaM hlift
    obtain ⟨hw, hs'⟩ := Returns.pure k3
    exact ⟨hw, hs'.trans h3⟩
  rw [hmk]; exact ⟨goal.1, goal.2.trans hs2⟩

/-! ## Step rewrites for the root form -/

set_option maxHeartbeats 4000000 in
theorem memoryUncached_memoryE (rec : TranslateFn) (dom wa wd wen ra : Lean.Expr)
    (aw dw : Nat) (hint : String) (top named : Bool) :
    translateMemoryUncachedWith rec aw dw (memoryE dom aw dw wa wd wen ra)
        hint top named =
      (do
        let waW ← rec wa "mem_waddr" false false
        let wdW ← rec wd "mem_wdata" false false
        let weW ← rec wen "mem_we" false false
        let raW ← rec ra "mem_raddr" false false
        CompilerM.emitMemory hint aw dw "clk" (.ref waW) (.ref wdW) (.ref weW)
          (.ref raW) (named := named)) := rfl

set_option maxHeartbeats 4000000 in
theorem memory_step (rec : TranslateFn) (dom wa wd wen ra : Lean.Expr) (aw dw : Nat)
    (hdom : (dom.isFVar || dom.isBVar) = true) (haw : 0 < aw) (hdw : 0 < dw)
    (hint : String) (top named : Bool) :
    translateStepWith translateFallback rec (memoryE dom aw dw wa wd wen ra)
        hint top named =
      translateControlCachedWith (translateMemoryUncachedWith rec aw dw)
        (memoryE dom aw dw wa wd wen ra) hint top named := by
  have shape : translateCoreShape (memoryE dom aw dw wa wd wen ra) = false := rfl
  have core : translateCore rec (memoryE dom aw dw wa wd wen ra) hint top named =
    pure none := rfl
  have control : isBoolControl (memoryE dom aw dw wa wd wen ra) = false := rfl
  have mux : canonicalMuxType? (memoryE dom aw dw wa wd wen ra) = none := rfl
  have setw : canonicalSetWidth? (memoryE dom aw dw wa wd wen ra) = none := rfl
  have reg : canonicalRegister? (memoryE dom aw dw wa wd wen ra) = none := rfl
  have regEn : canonicalRegisterEnable? (memoryE dom aw dw wa wd wen ra) = none := rfl
  have loopR : canonicalLoopRegister? (memoryE dom aw dw wa wd wen ra) = none := rfl
  have cdo1 : canonicalCircuitDo? (memoryE dom aw dw wa wd wen ra) = none := rfl
  have cdo2 : canonicalCircuitDo2? (memoryE dom aw dw wa wd wen ra) = none := rfl
  have mem := canonicalMemory?_memoryE (wa := wa) (wd := wd) (wen := wen) (ra := ra)
    hdom haw hdw
  have step : translateStepWith translateFallback rec
      (memoryE dom aw dw wa wd wen ra) hint top named =
      translateFallback rec (memoryE dom aw dw wa wd wen ra) hint top named := by
    simp [translateStepWith, shape, core]
    rfl
  rw [step]
  simp only [translateFallback, control, Bool.false_eq_true, if_false, mux, setw,
    reg, regEn, loopR, cdo1, cdo2, mem]

/-! ## The monolith -/

def MemoryPreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (dom : Lean.Expr) (aw dw : Nat) (waId wdId wenId raId : FVarId),
    (dom.isFVar || dom.isBVar) = true → 0 < aw → 0 < dw →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      memoryE dom aw dw (.fvar waId) (.fvar wdId) (.fvar wenId) (.fvar raId) →
    ∃ (nm rdW waW wdW wenW raW : String),
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (wav rav : BitVec aw) (wdv : BitVec dw) (wev : Bool),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    p.bits waId = some ⟨aw, wav⟩ → p.bits wdId = some ⟨dw, wdv⟩ →
    p.bools wenId = some wev → p.bits raId = some ⟨aw, rav⟩ →
    m.body = memBody nm "clk" waW wdW wenW raW rdW aw dw ∧
    rdW ≠ "out" ∧ waW ≠ "out" ∧ wdW ≠ "out" ∧ wenW ≠ "out" ∧ raW ≠ "out" ∧
    env0 waW = wav.toNat ∧ env0 wdW = wdv.toNat ∧
    env0 wenW = (if wev then 1 else 0) ∧ env0 raW = rav.toNat

set_option maxHeartbeats 2000000 in
theorem synthesizeMixedCertified_memory_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    MemoryPreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, _⟩ :=
    synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom aw dw waId wdId wenId raId hdom haw hdw qeq
  -- Static decomposition at the zero valuation: the run's context and
  -- state do not depend on the port values.
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)
    (bools := fun _ => false) (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨rdW, sm, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have stepEq : translateExprToWire
      (memoryE dom aw dw (.fvar waId) (.fvar wdId) (.fvar wenId) (.fvar raId))
        "out" false true =
      translateControlCachedWith
        (translateMemoryUncachedWith (translateFuelFix translateStep 1048575) aw dw)
        (memoryE dom aw dw (.fvar waId) (.fvar wdId) (.fvar wenId) (.fvar raId))
        "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (memoryE dom aw dw (.fvar waId) (.fvar wdId) (.fvar wenId) (.fvar raId))
      "out" false true = _
    rw [memory_step _ dom _ _ _ _ aw dw hdom haw hdw]
  rw [stepEq] at tr
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord
      = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec rdW rfl
    rw [record0] at dead
    simp at dead
  rw [memoryUncached_memoryE] at missRun
  -- The four operand reads, opaque for now.
  obtain ⟨waW, s1, r1, k1⟩ := Returns.bind missRun
  obtain ⟨wdW, s2, r2, k2⟩ := Returns.bind k1
  obtain ⟨wenW, s3, r3, k3⟩ := Returns.bind k2
  obtain ⟨raW, s4, r4, k4⟩ := Returns.bind k3
  -- The emission, on the (opaque) post-operand state.
  obtain ⟨hrdW, hsmR⟩ := emitMemory_returns k4
  have hrec := recordTranslation_returns record
  obtain ⟨hrE1, hrE2⟩ := emitMemoryC_spec "out" aw dw "clk"
    (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) true s4
  have hstr : (toString "out" ++ toString "_rdata" : String) = "out_rdata" := rfl
  rw [hstr] at hrE1 hrE2
  have hrdWm : rdW = (CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
      ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).1 := by
    rw [hrdW, hrE1]
  have smModule : sm.module =
      ((CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
        ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.module.addWire
          { name := rdW, ty := .bitVector dw }).addStmt
        (.memory (CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1
          aw dw "clk" (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) rdW) := by
    rw [hrec, hsmR, hrE2, ← hrdWm]
  have fn1 := CircuitM.freshName_spec (CircuitM.sanitizeName "out") true s4
  have fn2 := CircuitM.freshName_spec (CircuitM.sanitizeName "out_rdata") true
    ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)
  have stBody : st.module.body =
      .assign "out" (.ref rdW) ::
        .memory (CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1
          aw dw "clk" (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) rdW ::
          s4.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state]
    show _ :: (sm.module.addOutput _).body = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).body = mo.body from
      fun _ _ => rfl, smModule]
    show _ :: (_ :: (CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
      ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.module.body) = _
    rw [fn2.2.2, fn1.2.2]
  have mBody : m.body = s4.module.body.reverse ++
      [.memory (CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1
        aw dw "clk" (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) rdW,
       .assign "out" (.ref rdW)] := by
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).body = _
    simp only [Sparkle.IR.AST.Module.finalize,
      (Tools.ShippingEntrySoundness.addClockReset_facts st.module).1, stBody]
    simp
  have rdNotOut : rdW ≠ "out" := by
    intro eq
    have alloc := CircuitM.freshName_allocated (CircuitM.sanitizeName "out_rdata") true
      ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)
    rw [← hrdWm, eq] at alloc
    exact not_allocated_out alloc
  refine ⟨(CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1,
    rdW, waW, wdW, wenW, raW, ?_⟩
  -- The runtime half: pin the operand reads to the input wires.
  intro bools bits env0 wav rav wdv wev a p adm hwa0 hwd0 hwen0 hra0
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  -- Transport the operand runs to the real valuation's (equal) context/state.
  rw [pc, ps] at r1
  have hwaB := prepared.1.bits waId aw wav hwa0
  obtain ⟨waW', waBound, waDecl, waVal⟩ := hwaB
  have hwdB := prepared.1.bits wdId dw wdv hwd0
  obtain ⟨wdW', wdBound, wdDecl, wdVal⟩ := hwdB
  have hwenB := prepared.1.bool wenId wev hwen0
  obtain ⟨wenW', wenBound, wenDecl, wenVal⟩ := hwenB
  have hraB := prepared.1.bits raId aw rav hra0
  obtain ⟨raW', raBound, raDecl, raVal⟩ := hraB
  have fuelEq : translateFuelFix translateStep 1048575 =
      translateStepWith translateFallback (translateFuelFix translateStep 1048574) := rfl
  rw [fuelEq] at r1 r2 r3 r4
  obtain ⟨hwaW, hs1⟩ := translateStep_fvar_returns waBound r1
  subst hs1
  rw [pc] at r2
  obtain ⟨hwdW, hs2⟩ := translateStep_fvar_returns wdBound r2
  subst hs2
  rw [pc] at r3
  obtain ⟨hwenW, hs3⟩ := translateStep_fvar_returns wenBound r3
  subst hs3
  rw [pc] at r4
  obtain ⟨hraW, hs4⟩ := translateStep_fvar_returns raBound r4
  have hbodyZ : (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.module.body
      = [] := by
    rw [prepared.2.2.1]; rfl
  have hs4body : s4.module.body = [] := by
    rw [hs4]
    exact hbodyZ
  have inputNotOut : ∀ (q : Sparkle.IR.AST.Port),
      q ∈ (prepare bools bits (bs.zip ids)
        (start (entryCompilerState false cache) declName.toString)).state.module.wires →
      q.name ≠ "out" := by
    intro q hq eq
    have alloc := prepare_wires_allocated bools bits (bs.zip ids) _
      (by rw [show (start (entryCompilerState false cache) declName.toString).state =
          CircuitM.init declName.toString from rfl, init_wires]
          intro x hx; cases hx) q hq
    rw [eq] at alloc
    exact not_allocated_out alloc
  refine ⟨?_, rdNotOut, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mBody, hs4body]
    subst hwaW hwdW hwenW hraW
    rfl
  · subst hwaW; exact inputNotOut _ waDecl
  · subst hwdW; exact inputNotOut _ wdDecl
  · subst hwenW; exact inputNotOut _ wenDecl
  · subst hraW; exact inputNotOut _ raDecl
  · subst hwaW; exact waVal
  · subst hwdW; exact wdVal
  · subst hwenW; exact wenVal
  · subst hraW; exact raVal

/-! ## The cone monolith: all four operands through the unified contract -/

/-- `memNexts` walks past a pure-assign prefix. -/
theorem memNexts_skip_assigns {we : WEnv} {mems : MEnv} {env : Env} :
    ∀ {pre rest : List Stmt}, (∀ st ∈ pre, ∃ l r, st = .assign l r) →
      memNexts we (pre ++ rest) mems env = memNexts we rest mems env
  | [], rest, _ => rfl
  | st :: pre, rest, h => by
    obtain ⟨l, r, rfl⟩ := h st List.mem_cons_self
    show memNexts we (pre ++ rest) mems env = _
    exact memNexts_skip_assigns (fun q hq => h q (List.mem_cons_of_mem _ hq))

def MemoryConePreserves (declName : Name) (bs : List (Name × MixedGateBinder))
    (body : Lean.Expr) (m : Sparkle.IR.AST.Module) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
  ∃ cache : IO.Ref (ExprStructMap String),
    ∀ (dom : Lean.Expr) (kb kv : Nat) (vw : Nat → Nat) (binp vinp : Nat → FVarId)
      {aw dw : Nat} (eWA : Term (.bits aw)) (eWD : Term (.bits dw))
      (eWEN : Term .bool) (eRA : Term (.bits aw)),
    (dom.isFVar || dom.isBVar) = true → 0 < aw → 0 < dw →
    eWA.WF kb kv vw → eWD.WF kb kv vw → eWEN.WF kb kv vw → eRA.WF kb kv vw →
    instFVars (ids.map Lean.Expr.fvar).toArray 0 body =
      memoryE dom aw dw
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eWA)
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eWD)
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eWEN)
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eRA) →
    ∃ (nm rdW : String), rdW ≠ "out" ∧
    ∀ (bools : FVarId → Bool) (bits : (id : FVarId) → (n : Nat) → BitVec n)
      (env0 : Env) (mems : MEnv)
      (bvals : Nat → Bool) (vvals : (j : Nat) → (n : Nat) → BitVec n),
    let a := start (entryCompilerState false cache) declName.toString
    let p := prepare bools bits (bs.zip ids) a
    Admissible bools bits env0 (bs.zip ids) a →
    (∀ j, j < kb → p.bools (binp j) = some (bvals j)) →
    (∀ j, j < kv → p.bits (vinp j) = some ⟨vw j, vvals j (vw j)⟩) →
    ∃ envF, stepModule (weOf m) m.body env0 mems =
        some (envF,
          [(rdW, mask dw (mems nm (mask aw (eval bvals vvals eRA).toNat)))],
          if eval bvals vvals eWEN then
            (fun n i => if n = nm ∧ i = mask aw (eval bvals vvals eWA).toNat
              then mask dw (eval bvals vvals eWD).toNat else mems n i)
          else mems) ∧
      envF "out" = env0 rdW

set_option maxHeartbeats 4000000 in
theorem synthesizeMixedCertified_memoryCone_sound {logProf declName bs body m d}
    (hr : MReturns (synthesizeMixedCertified
      (fun e hint top named => translateExprToWire e hint top named) logProf declName bs body)
      (m, d)) :
    MemoryConePreserves declName bs body m := by
  obtain ⟨ids, cache, returned, st, nd, len, run, hm, _, _⟩ :=
    synthesizeMixedCertified_returns hr
  refine ⟨ids, nd, len, cache, ?_⟩
  intro dom kb kv vw binp vinp aw dw eWA eWD eWEN eRA hdom haw hdw hWA hWD hWEN hRA qeq
  have leaf := prepare_returns (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString)
    (bools := fun _ => false) (bits := fun _ _ => 0) run
  rw [qeq] at leaf
  obtain ⟨rdW, sm, ty, tr, freshOut, ht, hty⟩ := emitLeaves_single leaf
  have stepEq : translateExprToWire
      (memoryE dom aw dw
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eWA)
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eWD)
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eWEN)
        (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eRA))
        "out" false true =
      translateControlCachedWith
        (translateMemoryUncachedWith (translateFuelFix translateStep 1048575) aw dw)
        (memoryE dom aw dw
          (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eWA)
          (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eWD)
          (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eWEN)
          (quote dom (fun j => .fvar (binp j)) (fun j => .fvar (vinp j)) eRA))
        "out" false true := by
    show translateStepWith translateFallback (translateFuelFix translateStep 1048575)
      (memoryE dom aw dw _ _ _ _) "out" false true = _
    rw [memory_step _ dom _ _ _ _ aw dw hdom haw hdw]
  rw [stepEq] at tr
  have empty0 := empty_layout (entryCompilerState false cache) declName.toString (fun _ => 0)
  have record0 : (prepare (fun _ => false) (fun _ _ => 0) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).state.translateRecord
      = {} :=
    (prepare_layout (bs.zip ids) _ empty0.1 empty0.2 (admissible_zero _ _)).2.2.2
  rcases translateControlCachedWith_returns tr with hit | ⟨smR, missRun, record⟩
  · obtain ⟨-, hrec⟩ := cacheLookupValidated_returns hit
    have dead := hrec rdW rfl
    rw [record0] at dead
    simp at dead
  rw [memoryUncached_memoryE] at missRun
  obtain ⟨waW, s1, rc1, k1⟩ := Returns.bind missRun
  obtain ⟨wdW, s2, rc2, k2⟩ := Returns.bind k1
  obtain ⟨wenW, s3, rc3, k3⟩ := Returns.bind k2
  obtain ⟨raW, s4, rc4, k4⟩ := Returns.bind k3
  obtain ⟨hrdW, hsmR⟩ := emitMemory_returns k4
  have hrec := recordTranslation_returns record
  obtain ⟨hrE1, hrE2⟩ := emitMemoryC_spec "out" aw dw "clk"
    (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) true s4
  have hstr : (toString "out" ++ toString "_rdata" : String) = "out_rdata" := rfl
  rw [hstr] at hrE1 hrE2
  have hrdWm : rdW = (CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
      ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).1 := by
    rw [hrdW, hrE1]
  have smModule : sm.module =
      ((CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
        ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.module.addWire
          { name := rdW, ty := .bitVector dw }).addStmt
        (.memory (CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1
          aw dw "clk" (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) rdW) := by
    rw [hrec, hsmR, hrE2, ← hrdWm]
  have fn1 := CircuitM.freshName_spec (CircuitM.sanitizeName "out") true s4
  have fn2 := CircuitM.freshName_spec (CircuitM.sanitizeName "out_rdata") true
    ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)
  have stBody : st.module.body =
      .assign "out" (.ref rdW) ::
        .memory (CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1
          aw dw "clk" (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) rdW ::
          s4.module.body := by
    rw [ht, emitAssign_body_cons, addOutput_state]
    show _ :: (sm.module.addOutput _).body = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).body = mo.body from
      fun _ _ => rfl, smModule]
    show _ :: (_ :: (CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
      ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.module.body) = _
    rw [fn2.2.2, fn1.2.2]
  have stWires : st.module.wires =
      { name := rdW, ty := .bitVector dw } :: s4.module.wires := by
    rw [ht, emitAssign_wires, addOutput_state]
    show (sm.module.addOutput _).wires = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addOutput q).wires = mo.wires from
      fun _ _ => rfl, smModule]
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addStmt q).wires = mo.wires from
      fun _ _ => rfl]
    show ((CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
      ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.module.addWire
        { name := rdW, ty := .bitVector dw }).wires = _
    rw [show ∀ (mo : Sparkle.IR.AST.Module) q, (mo.addWire q).wires = q :: mo.wires from
      fun _ _ => rfl, fn2.2.2, fn1.2.2]
  have mBody : m.body = s4.module.body.reverse ++
      [.memory (CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1
        aw dw "clk" (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) rdW,
       .assign "out" (.ref rdW)] := by
    rw [hm]
    show ((addClockResetIfSequential st.module).finalize).body = _
    simp only [Sparkle.IR.AST.Module.finalize,
      (Tools.ShippingEntrySoundness.addClockReset_facts st.module).1, stBody]
    simp
  have rdFreshMid : ((CircuitM.freshName (CircuitM.sanitizeName "out") true
      s4).2).usedNames.contains rdW = false := by
    rw [hrdWm]; exact fn2.1
  have rdNotS4 : s4.usedNames.contains rdW = false := by
    rcases h : s4.usedNames.contains rdW with _ | _
    · rfl
    · have : ((CircuitM.freshName (CircuitM.sanitizeName "out") true
          s4).2).usedNames.contains rdW = true := by
        rw [fn1.2.1]
        simp [Std.HashSet.contains_insert, h]
      rw [rdFreshMid] at this
      cases this
  have rdNotOut : rdW ≠ "out" := by
    intro eq
    have alloc := CircuitM.freshName_allocated (CircuitM.sanitizeName "out_rdata") true
      ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)
    rw [← hrdWm, eq] at alloc
    exact not_allocated_out alloc
  refine ⟨(CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1,
    rdW, rdNotOut, ?_⟩
  intro bools bits env0 mems bvals vvals a p adm hb0 hv0
  have empty := empty_layout (entryCompilerState false cache) declName.toString env0
  have prepared := prepare_layout (bs.zip ids)
    (start (entryCompilerState false cache) declName.toString) empty.1 empty.2 adm
  obtain ⟨pc, ps⟩ := prepare_const (fun _ => false) bools (fun _ _ => 0) bits
    (bs.zip ids) _ _ rfl rfl
  rw [pc, ps] at rc1
  rw [pc] at rc2 rc3 rc4
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
  have contract1 := fuel_contract 1048575
    (ctx := (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context)
    (we := declaredWidths st) (mems := mems) (initial := env0) (dom := dom) hb' hv' eWA hWA
  have contract2 := fuel_contract 1048575
    (ctx := (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context)
    (we := declaredWidths st) (mems := mems) (initial := env0) (dom := dom) hb' hv' eWD hWD
  have contract3 := fuel_contract 1048575
    (ctx := (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context)
    (we := declaredWidths st) (mems := mems) (initial := env0) (dom := dom) hb' hv' eWEN hWEN
  have contract4 := fuel_contract 1048575
    (ctx := (prepare bools bits (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString)).context)
    (we := declaredWidths st) (mems := mems) (initial := env0) (dom := dom) hb' hv' eRA hRA
  have lookup := lookup_of_ports prepared.1 prepared.2.1
  have f1 := contract1.frame "mem_waddr" false false _ s1 waW lookup rc1
  have f2 := contract2.frame "mem_wdata" false false s1 s2 wdW (lookup.transfer f1) rc2
  have f3 := contract3.frame "mem_we" false false s2 s3 wenW
    ((lookup.transfer f1).transfer f2) rc3
  have f4 := contract4.frame "mem_raddr" false false s3 s4 raW
    (((lookup.transfer f1).transfer f2).transfer f3) rc4
  have wiresS4 : WiresOk s4 := f4.wires (f3.wires (f2.wires (f1.wires prepared.2.1)))
  have rdNotS4W : rdW ∉ s4.module.wires.map (·.name) := by
    intro hmem
    obtain ⟨q, hq, eq⟩ := List.mem_map.mp hmem
    have := wiresS4.2 q hq
    rw [eq, rdNotS4] at this
    cases this
  have stUsed : st.usedNames = ((((CircuitM.freshName (CircuitM.sanitizeName "out") true
      s4).2).usedNames.insert rdW).insert "out") := by
    rw [ht, emitAssign_usedNames, addOutput_state]
    show (sm.usedNames.insert "out") = _
    rw [hrec, hsmR, hrE2]
    show (((CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
      ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.usedNames).insert
        "out") = _
    rw [fn2.2.1, ← hrdWm]
  have wiresSt : WiresOk st := by
    constructor
    · rw [stWires]
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨rdNotS4W, wiresS4.1⟩
    · intro q hq
      rw [stWires] at hq
      rw [stUsed]
      rcases List.mem_cons.mp hq with rfl | hq
      · simp [Std.HashSet.contains_insert]
      · have hs4u := wiresS4.2 q hq
        have : ((CircuitM.freshName (CircuitM.sanitizeName "out") true
            s4).2).usedNames.contains q.name = true := by
          rw [fn1.2.1]
          simp [Std.HashSet.contains_insert, hs4u]
        simp [Std.HashSet.contains_insert, this]
  have inv0 : Inv _ (inputValues _ _) (declaredWidths st) mems env0 _ env0 :=
    initial_unified
      (by rw [prepared.2.2.1]; rfl)
      (by rw [prepared.2.2.2]; rfl)
      separate
      (prepared.1.inputs prepared.2.1
        (by intro q hq; rw [stWires]
            exact List.mem_cons_of_mem _
              (f4.decls q (f3.decls q (f2.decls q (f1.decls q hq)))))
        (declaredWidths_agree wiresSt))
  have widths4 : ScalarWidthsAgree (declaredWidths st) s4 := by
    intro q hq
    exact declaredWidths_agree wiresSt q (by
      rw [stWires]; exact List.mem_cons_of_mem _ hq)
  have widths1 : ScalarWidthsAgree (declaredWidths st) s1 := fun q hq =>
    widths4 q (f4.decls q (f3.decls q (f2.decls q hq)))
  have widths2 : ScalarWidthsAgree (declaredWidths st) s2 := fun q hq =>
    widths4 q (f4.decls q (f3.decls q hq))
  have widths3 : ScalarWidthsAgree (declaredWidths st) s3 := fun q hq =>
    widths4 q (f4.decls q hq)
  have o1 := contract1.sem "mem_waddr" false false _ s1 waW env0 inv0 widths1 rc1
  obtain ⟨res1, inv1, val1, fvals1⟩ := o1.execution
  have o2 := contract2.sem "mem_wdata" false false s1 s2 wdW res1 inv1 widths2 rc2
  obtain ⟨res2, inv2, val2, fvals2⟩ := o2.execution
  have o3 := contract3.sem "mem_we" false false s2 s3 wenW res2 inv2 widths3 rc3
  obtain ⟨res3, inv3, val3, fvals3⟩ := o3.execution
  have o4 := contract4.sem "mem_raddr" false false s3 s4 raW res3 inv3 widths4 rc4
  obtain ⟨res4, inv4, val4, fvals4⟩ := o4.execution
  have ordered1 := fuel_orders 1048575 (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' eWA hWA "mem_waddr" false _ s1 waW env0 rc1 inv0
    widths1 (OrderInv.empty (by rw [prepared.2.2.1]; rfl))
  have ordered2 := fuel_orders 1048575 (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' eWD hWD "mem_wdata" false s1 s2 wdW res1 rc2 inv1
    widths2 ordered1
  have ordered3 := fuel_orders 1048575 (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' eWEN hWEN "mem_we" false s2 s3 wenW res2 rc3 inv2
    widths3 ordered2
  have ordered4 := fuel_orders 1048575 (we := declaredWidths st) (mems := mems)
    (initial := env0) (dom := dom) hb' hv' eRA hRA "mem_raddr" false s3 s4 raW res3 rc4 inv3
    widths4 ordered3
  have seqS4 : SeqBody s4.module.finalize.body := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := inv4.typed stq (by
      change stq ∈ s4.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact Or.inl ⟨l, rhs, eq⟩
  have preAssigns : ∀ stq ∈ s4.module.finalize.body, ∃ l rhs, stq = .assign l rhs := by
    intro stq hq
    obtain ⟨l, rhs, eq, _⟩ := inv4.typed stq (by
      change stq ∈ s4.module.body.reverse at hq
      exact List.mem_reverse.mp hq)
    exact ⟨l, rhs, eq⟩
  have preEq : s4.module.finalize.body = s4.module.body.reverse := by
    simp [Sparkle.IR.AST.Module.finalize]
  have rdNotW : rdW ∉ Sparkle.IR.Reorder.writesOf s4.module.finalize.body := by
    intro hwr
    have hf := writes_mem_footprint hwr
    rw [preEq] at hf
    have hfp := (footprint_reverse_mem _ _).mp hf
    have := ordered4.2 rdW hfp
    rw [rdNotS4] at this
    cases this
  have runs4 : evalAssigns (declaredWidths st) mems s4.module.finalize.body env0 =
      some res4 := inv4.runs
  have resRd : res4 rdW = env0 rdW :=
    Tools.ShippingRegisterSoundness.evalAssigns_preserved seqS4 runs4 rdNotW
  -- Operand values at the settled pre-body environment.
  have waUsed1 : s1.usedNames.contains waW = true := o1.used
  have resWA : res4 waW = (eval bvals vvals eWA).toNat := by
    rw [fvals4 waW (f3.used waW (f2.used waW waUsed1)),
      fvals3 waW (f2.used waW waUsed1), fvals2 waW waUsed1]
    exact val1
  have wdUsed2 : s2.usedNames.contains wdW = true := o2.used
  have resWD : res4 wdW = (eval bvals vvals eWD).toNat := by
    rw [fvals4 wdW (f3.used wdW wdUsed2), fvals3 wdW wdUsed2]
    exact val2
  have wenUsed3 : s3.usedNames.contains wenW = true := o3.used
  have resWEN : res4 wenW =
      Tools.ShippingMuxLoweringSoundness.encodeBool (eval bvals vvals eWEN) := by
    rw [fvals4 wenW wenUsed3]
    exact val3
  have resRA : res4 raW = (eval bvals vvals eRA).toNat := val4
  -- Assemble the step.
  let envF : Env := fun n => if n = "out" then res4 rdW else res4 n
  have evalFull : evalAssigns (declaredWidths st) mems m.body env0 = some envF := by
    rw [mBody, ← preEq,
      Tools.ShippingRegisterSoundness.evalAssigns_append seqS4, runs4]
    show evalAssigns _ mems
      (.memory _ aw dw "clk" (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) rdW ::
        .assign "out" (.ref rdW) :: []) res4 = _
    simp [evalAssigns, evalExpr, envF]
  have envFwa : envF waW = (eval bvals vvals eWA).toNat := by
    have hne : waW ≠ "out" := by
      intro eq
      have used4 := f4.used waW (f3.used waW (f2.used waW waUsed1))
      have : sm.usedNames.contains waW = true := by
        rw [hrec, hsmR, hrE2]
        show ((CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
          ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.usedNames).contains
            waW = true
        rw [fn2.2.1, fn1.2.1]
        simp [Std.HashSet.contains_insert, used4]
      rw [eq, freshOut] at this
      cases this
    simp only [envF, if_neg hne]
    exact resWA
  have envFwd : envF wdW = (eval bvals vvals eWD).toNat := by
    have hne : wdW ≠ "out" := by
      intro eq
      have used4 := f4.used wdW (f3.used wdW wdUsed2)
      have : sm.usedNames.contains wdW = true := by
        rw [hrec, hsmR, hrE2]
        show ((CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
          ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.usedNames).contains
            wdW = true
        rw [fn2.2.1, fn1.2.1]
        simp [Std.HashSet.contains_insert, used4]
      rw [eq, freshOut] at this
      cases this
    simp only [envF, if_neg hne]
    exact resWD
  have envFwen : envF wenW =
      Tools.ShippingMuxLoweringSoundness.encodeBool (eval bvals vvals eWEN) := by
    have hne : wenW ≠ "out" := by
      intro eq
      have used4 := f4.used wenW wenUsed3
      have : sm.usedNames.contains wenW = true := by
        rw [hrec, hsmR, hrE2]
        show ((CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
          ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.usedNames).contains
            wenW = true
        rw [fn2.2.1, fn1.2.1]
        simp [Std.HashSet.contains_insert, used4]
      rw [eq, freshOut] at this
      cases this
    simp only [envF, if_neg hne]
    exact resWEN
  have envFra : envF raW = (eval bvals vvals eRA).toNat := by
    have hne : raW ≠ "out" := by
      intro eq
      have used4 := o4.used
      have : sm.usedNames.contains raW = true := by
        rw [hrec, hsmR, hrE2]
        show ((CircuitM.freshName (CircuitM.sanitizeName "out_rdata") true
          ((CircuitM.freshName (CircuitM.sanitizeName "out") true s4).2)).2.usedNames).contains
            raW = true
        rw [fn2.2.1, fn1.2.1]
        simp [Std.HashSet.contains_insert, used4]
      rw [eq, freshOut] at this
      cases this
    simp only [envF, if_neg hne]
    exact resRA
  have nexts : regNexts (declaredWidths st) mems m.body envF =
      some [(rdW, mask dw (mems
        (CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1
        (mask aw (eval bvals vvals eRA).toNat)))] := by
    rw [mBody, ← preEq,
      Tools.ShippingRegisterSoundness.regNexts_skip_assigns preAssigns]
    show regNexts _ mems
      (.memory _ aw dw "clk" (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) rdW ::
        .assign "out" (.ref rdW) :: []) envF = _
    simp [regNexts, syncReadLatches, evalExpr, envFra]
  have memn : memNexts (declaredWidths st) m.body mems envF =
      some (if eval bvals vvals eWEN then
        (fun n i => if n = (CircuitM.freshName (CircuitM.sanitizeName "out") true s4).1
            ∧ i = mask aw (eval bvals vvals eWA).toNat
          then mask dw (eval bvals vvals eWD).toNat else mems n i)
        else mems) := by
    rw [mBody, ← preEq, memNexts_skip_assigns preAssigns]
    show memNexts _
      (.memory _ aw dw "clk" (.ref waW) (.ref wdW) (.ref wenW) (.ref raW) rdW ::
        .assign "out" (.ref rdW) :: []) mems envF = _
    cases hEn : eval bvals vvals eWEN <;>
      simp [memNexts, memWritePorts, evalPayload_ref, envFwa, envFwd, envFwen, hEn,
        Tools.ShippingMuxLoweringSoundness.encodeBool]
  have scalarSt : ScalarWires st := by
    intro q hq
    rw [stWires] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact Or.inr ⟨dw, rfl⟩
    · exact f4.scalar (f3.scalar (f2.scalar (f1.scalar (prepare_shape (bs.zip ids) _ (by
        intro q hq'
        rw [show (start (entryCompilerState false cache) declName.toString).state =
          CircuitM.init declName.toString from rfl, init_wires] at hq'
        cases hq')).1))) q hq
  have mWires : m.wires = st.module.wires.reverse := by
    rw [hm]
    simp only [Sparkle.IR.AST.Module.finalize,
      (Tools.ShippingEntrySoundness.addClockReset_facts st.module).2.1]
  have wm : weOf m = declaredWidths st := by
    rw [weOf_eq_moduleWidths (by
      intro q hq; rw [mWires, List.mem_reverse] at hq; exact scalarSt q hq)]
    exact moduleWidths_finish mWires wiresSt
  refine ⟨envF, ?_, by simp [envF, resRd]⟩
  rw [wm]
  unfold stepModule
  simp [evalFull, nexts, memn, bind]

/-! ## Dispatch from the real entry -/

theorem synthesizeFromConst_memory_sound {logProf declName ci bs body m d}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci) (m, d)) :
    MemoryPreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_memory_sound run

theorem synthesizeCombinationalCore_memory_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) →
        MemoryPreserves declName bs body m := by
  obtain ⟨logProf, ci, w1, w2, w3, get, run⟩ := synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape =>
    synthesizeFromConst_memory_sound old shape run.mreturns⟩

/-! ## Source-position plumbing and the entry endpoints -/

/-- The compiled module's body and per-cycle input-wire values, from the
real entry: the module IS the canonical memory body, with the operand
wires observing the source positions' values. -/
theorem memory_body_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)}
    {dpos wapos wdpos wenpos rapos : Nat} {aw dw : Nat}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, memoryE (inputExpr bs.length dpos) aw dw
      (inputExpr bs.length wapos) (inputExpr bs.length wdpos)
      (inputExpr bs.length wenpos) (inputExpr bs.length rapos)))
    (hdp : dpos < bs.length) (haw : 0 < aw) (hdw : 0 < dw)
    (hwa : ∃ name, bs[wapos]? = some (name, .bits aw))
    (hwd : ∃ name, bs[wdpos]? = some (name, .bits dw))
    (hwen : ∃ name, bs[wenpos]? = some (name, .bool))
    (hra : ∃ name, bs[rapos]? = some (name, .bits aw)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (nm rdW waW wdW wenW raW : String),
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (env0 : Env),
      SourceInputs declName bs ids cache bools bits env0 →
      m.body = memBody nm "clk" waW wdW wenW raW rdW aw dw ∧
      rdW ≠ "out" ∧ waW ≠ "out" ∧ wdW ≠ "out" ∧ wenW ≠ "out" ∧ raW ≠ "out" ∧
      env0 waW = (bits wapos aw).toNat ∧ env0 wdW = (bits wdpos dw).toNat ∧
      env0 wenW = (if bools wenpos then 1 else 0) ∧
      env0 raW = (bits rapos aw).toNat := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_memory_sound hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have hdom : ((inputExpr bs.length dpos).isFVar ||
      (inputExpr bs.length dpos).isBVar) = true := by
    simp only [inputExpr]
    rfl
  have mixedGate := memory_term_gate (d := d)
    (by rw [definition]; exact peel) hdom haw hdw hwa hwd hwen hra
  obtain ⟨ids, nd, len, cache, H⟩ := source bs _ oldGate mixedGate
  have hwaP := (List.getElem_of_getElem? hwa.choose_spec).choose
  have hwdP := (List.getElem_of_getElem? hwd.choose_spec).choose
  have hwenP := (List.getElem_of_getElem? hwen.choose_spec).choose
  have hraP := (List.getElem_of_getElem? hra.choose_spec).choose
  have qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0
      (memoryE (inputExpr bs.length dpos) aw dw
        (inputExpr bs.length wapos) (inputExpr bs.length wdpos)
        (inputExpr bs.length wenpos) (inputExpr bs.length rapos)) =
      memoryE (.fvar ids[dpos]!) aw dw (.fvar ids[wapos]!) (.fvar ids[wdpos]!)
        (.fvar ids[wenpos]!) (.fvar ids[rapos]!) := by
    rw [instFVars_memoryE, instantiated_input len hdp,
      instantiated_input len hwaP, instantiated_input len hwdP,
      instantiated_input len hwenP, instantiated_input len hraP]
  obtain ⟨nm, rdW, waW, wdW, wenW, raW, H⟩ := H (.fvar ids[dpos]!) aw dw
    ids[wapos]! ids[wdpos]! ids[wenpos]! ids[rapos]! (by rfl) haw hdw qeq
  refine ⟨ids, nd, len, cache, nm, rdW, waW, wdW, wenW, raW, ?_⟩
  intro bools bits env0 values
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  refine H (boolValues ids bools) (bitValues ids bits) env0
    (bits wapos aw) (bits rapos aw) (bits wdpos dw) (bools wenpos) values ?_ ?_ ?_ ?_
  · have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh
      (zip_member len hwa.choose_spec)
    simpa only [bitValues, index_fresh ids nd wapos (by omega)] using lookup
  · have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh
      (zip_member len hwd.choose_spec)
    simpa only [bitValues, index_fresh ids nd wdpos (by omega)] using lookup
  · have lookup := prepare_bool_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh
      (zip_member len hwen.choose_spec)
    simpa only [boolValues, index_fresh ids nd wenpos (by omega)] using lookup
  · have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh
      (zip_member len hra.choose_spec)
    simpa only [bitValues, index_fresh ids nd rapos (by omega)] using lookup

/-- **The memory endpoint at the real entry.** The compiled module's whole
`runModule` trace observes the source `Signal.memory` stream, for every
admissible seeding discipline, from a zeroed latch and array. -/
theorem memory_run_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)}
    {dpos wapos wdpos wenpos rapos : Nat} {aw dw : Nat}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, memoryE (inputExpr bs.length dpos) aw dw
      (inputExpr bs.length wapos) (inputExpr bs.length wdpos)
      (inputExpr bs.length wenpos) (inputExpr bs.length rapos)))
    (hdp : dpos < bs.length) (haw : 0 < aw) (hdw : 0 < dw)
    (hwa : ∃ name, bs[wapos]? = some (name, .bits aw))
    (hwd : ∃ name, bs[wdpos]? = some (name, .bits dw))
    (hwen : ∃ name, bs[wenpos]? = some (name, .bool))
    (hra : ∃ name, bs[rapos]? = some (name, .bits aw)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (rdW : String),
      ∀ {D : Sparkle.Core.Domain.DomainConfig}
        (boolsS : Nat → Sparkle.Core.Signal.Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n))
        (we : WEnv) (mems0 : MEnv) (k : Nat)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat),
      (∀ t stv, SourceInputs declName bs ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv rdW = stv rdW) →
      st0 rdW = 0 →
      (∀ n i, mems0 n i = 0) →
      ∃ envs, runModule we m.body seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" =
          ((Sparkle.Core.Signal.Signal.memory (bitsS wapos aw) (bitsS wdpos dw)
            (boolsS wenpos) (bitsS rapos aw)).val j).toNat := by
  obtain ⟨ids, nd, len, cache, nm, rdW, waW, wdW, wenW, raW, H⟩ :=
    memory_body_of_env hr env old peel hdp haw hdw hwa hwd hwen hra
  refine ⟨ids, nd, len, cache, rdW, ?_⟩
  intro D boolsS bitsS we mems0 k seed st0 hseed hst0 hmems0
  have h0 := H (fun i => (boolsS i).val (k - 1 - 0))
    (fun i n => (bitsS i n).val (k - 1 - 0)) (seed 0 st0) (hseed 0 st0).1
  obtain ⟨hmb, rdNe, waNe, wdNe, wenNe, raNe, -, -, -, -⟩ := h0
  rw [hmb]
  refine Tools.ShippingMemorySoundness.memory_run_val rdNe waNe wdNe wenNe raNe
    (bitsS wapos aw) (bitsS wdpos dw) (boolsS wenpos) (bitsS rapos aw)
    k seed st0 mems0 ?_ hst0 hmems0
  intro t stv
  have ht := H (fun i => (boolsS i).val (k - 1 - t))
    (fun i n => (bitsS i n).val (k - 1 - t)) (seed t stv) (hseed t stv).1
  obtain ⟨-, -, -, -, -, -, hwaV, hwdV, hwenV, hraV⟩ := ht
  exact ⟨(hseed t stv).2, hwaV, hwdV, hwenV, hraV⟩

/-! ## Cone dispatch and the per-cycle endpoint -/

theorem memoryCone_term_gate {d : DefinitionVal} {bs : List (Name × MixedGateBinder)}
    {dom : Lean.Expr} {aw dw : Nat} {kb kv : Nat} {vw : Nat → Nat}
    {bpos vpos : Nat → Nat} {eWA : Term (.bits aw)} {eWD : Term (.bits dw)}
    {eWEN : Term .bool} {eRA : Term (.bits aw)}
    (peel : mixedGatePeel d.value = some (bs, memoryE dom aw dw
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) eWA)
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) eWD)
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) eWEN)
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) eRA)))
    (hdom : (dom.isFVar || dom.isBVar) = true) (haw : 0 < aw) (hdw : 0 < dw)
    (hWA : eWA.WF kb kv vw) (hWD : eWD.WF kb kv vw)
    (hWEN : eWEN.WF kb kv vw) (hRA : eRA.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    mixedCertifiedShape? false [] (.defnInfo d) = some (bs, memoryE dom aw dw
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) eWA)
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) eWD)
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) eWEN)
      (quote dom (fun j => inputExpr bs.length (bpos j))
        (fun j => inputExpr bs.length (vpos j)) eRA)) := by
  have hbA := fun j hj => (hb j hj).elim fun name pos => input_bool_accepted
    (bs := bs) (j := bpos j) (name := name) pos
  have hvA := fun j hj => (hvp j hj).elim fun name pos => input_bits_accepted
    (bs := bs) (j := vpos j) (name := name) pos
  have root := unifiedMemoryRoot_memoryE (kinds := (bs.map Prod.snd).toArray) hdom haw hdw
    (unified_quote_accepted (dom := dom) hbA hvA eWA hWA)
    (unified_quote_accepted (dom := dom) hbA hvA eWD hWD)
    (unified_quote_accepted (dom := dom) hbA hvA eWEN hWEN)
    (unified_quote_accepted (dom := dom) hbA hvA eRA hRA)
  simp only [mixedCertifiedShape?, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, root, Bool.or_true, if_true]
  rfl

theorem synthesizeFromConst_memoryCone_sound {logProf declName ci bs body m d}
    (old : certifiedShape? false [] ci = none)
    (shape : mixedCertifiedShape? false [] ci = some (bs, body))
    (hr : MReturns (synthesizeFromConst
      (fun e hint top named => translateExprToWire e hint top named) logProf declName
      [] false true ci) (m, d)) :
    MemoryConePreserves declName bs body m := by
  unfold synthesizeFromConst at hr
  simp only [↓reduceIte, old, shape] at hr
  peel_bind hr
  obtain ⟨result, run, hr⟩ := MReturns.bind hr
  peel_bind hr
  have eq := MReturns.pure hr
  subst result
  exact synthesizeMixedCertified_memoryCone_sound run

theorem synthesizeCombinationalCore_memoryCone_sound {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {d : Design}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, d) w') :
    ∃ (ci : ConstantInfo) (w1 w2 : Void IO.RealWorld),
      RunsTo (getConstInfo declName) mctx mref cctx cref w1 ci w2 ∧
      ∀ bs body, certifiedShape? false [] ci = none →
        mixedCertifiedShape? false [] ci = some (bs, body) →
        MemoryConePreserves declName bs body m := by
  obtain ⟨logProf, ci, w1, w2, w3, get, run⟩ := synthesizeCombinationalCore_reads hr
  exact ⟨ci, w1, w2, get, fun _ _ old shape =>
    synthesizeFromConst_memoryCone_sound old shape run.mreturns⟩

/-- **Per-cycle cone-memory endpoint at the real entry.** Each cycle's
step latches the pre-write array at the read cone's value and lands an
enabled write of the data cone's value at the address cone's value. -/
theorem memoryCone_step_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)}
    {dpos : Nat} {aw dw kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {eWA : Term (.bits aw)} {eWD : Term (.bits dw)}
    {eWEN : Term .bool} {eRA : Term (.bits aw)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, memoryE (inputExpr bs.length dpos) aw dw
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eWA) (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eWD) (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eWEN) (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eRA)))
    (hdp : dpos < bs.length) (haw : 0 < aw) (hdw : 0 < dw)
    (hWA : eWA.WF kb kv vw) (hWD : eWD.WF kb kv vw)
    (hWEN : eWEN.WF kb kv vw) (hRA : eRA.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (nm rdW : String), rdW ≠ "out" ∧
      ∀ (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n)
        (env0 : Env) (mems : MEnv),
      SourceInputs declName bs ids cache bools bits env0 →
      ∃ envF, stepModule (weOf m) m.body env0 mems =
          some (envF,
            [(rdW, mask dw (mems nm (mask aw
              (eval (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) eRA).toNat)))],
            if eval (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) eWEN then
              (fun n i => if n = nm ∧ i = mask aw
                  (eval (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) eWA).toNat
                then mask dw
                  (eval (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) eWD).toNat
                else mems n i)
            else mems) ∧
        envF "out" = env0 rdW := by
  obtain ⟨ci, w1, w2, get, source⟩ := synthesizeCombinationalCore_memoryCone_sound hr
  obtain ⟨d, rfl, definition⟩ := env w1 ci w2 get
  have oldGate : certifiedShape? false [] (.defnInfo d) = none := old d definition
  have hdom : ((inputExpr bs.length dpos).isFVar ||
      (inputExpr bs.length dpos).isBVar) = true := by
    simp only [inputExpr]
    rfl
  have mixedGate := memoryCone_term_gate (d := d)
    (by rw [definition]; exact peel) hdom haw hdw hWA hWD hWEN hRA hb hvp
  obtain ⟨ids, nd, len, cache, H⟩ := source bs _ oldGate mixedGate
  have qeq : instFVars (ids.map Lean.Expr.fvar).toArray 0
      (memoryE (inputExpr bs.length dpos) aw dw
        (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eWA) (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eWD) (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eWEN) (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eRA)) =
      memoryE (.fvar ids[dpos]!) aw dw
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => .fvar ids[vpos j]!) eWA)
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => .fvar ids[vpos j]!) eWD)
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => .fvar ids[vpos j]!) eWEN)
        (quote (.fvar ids[dpos]!) (fun j => .fvar ids[bpos j]!)
          (fun j => .fvar ids[vpos j]!) eRA) := by
    rw [instFVars_memoryE, instantiated_input len hdp]
    have hbi : ∀ j, j < kb → instFVars (ids.map Lean.Expr.fvar).toArray 0
        (inputExpr bs.length (bpos j)) = .fvar ids[bpos j]! := by
      intro j hj
      obtain ⟨name, pos⟩ := hb j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
    have hvi : ∀ j, j < kv → instFVars (ids.map Lean.Expr.fvar).toArray 0
        (inputExpr bs.length (vpos j)) = .fvar ids[vpos j]! := by
      intro j hj
      obtain ⟨name, pos⟩ := hvp j hj
      exact instantiated_input len (List.getElem_of_getElem? pos).choose
    rw [instantiated_quote hbi hvi eWA hWA, instantiated_quote hbi hvi eWD hWD,
      instantiated_quote hbi hvi eWEN hWEN, instantiated_quote hbi hvi eRA hRA,
      instantiated_input len hdp]
  obtain ⟨nm, rdW, rdNe, H⟩ := H (.fvar ids[dpos]!) kb kv vw
    (fun j => ids[bpos j]!) (fun j => ids[vpos j]!) eWA eWD eWEN eRA
    (by rfl) haw hdw hWA hWD hWEN hRA qeq
  refine ⟨ids, nd, len, cache, nm, rdW, rdNe, ?_⟩
  intro bools bits env0 mems values
  have fresh : ((bs.zip ids).map Prod.snd).Nodup := by rw [zip_ids len]; exact nd
  refine H (boolValues ids bools) (bitValues ids bits) env0 mems
    (fun j => bools (bpos j)) (fun j n => bits (vpos j) n) values ?_ ?_
  · intro j hj
    obtain ⟨name, pos⟩ := hb j hj
    have lookup := prepare_bool_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [boolValues, index_fresh ids nd (bpos j)
      (by have := (List.getElem_of_getElem? pos).choose; omega)] using lookup
  · intro j hj
    obtain ⟨name, pos⟩ := hvp j hj
    have lookup := prepare_bits_lookup (bools := boolValues ids bools)
      (bits := bitValues ids bits) (bs.zip ids)
      (start (entryCompilerState false cache) declName.toString) fresh (zip_member len pos)
    simpa only [bitValues, index_fresh ids nd (vpos j)
      (by have := (List.getElem_of_getElem? pos).choose; omega)] using lookup

/-- **Cone-memory trace endpoint at the real entry.** The whole
`runModule` trace follows the joint latch/array recurrence driven by the
four cones' per-cycle values. -/
theorem memoryCone_run_of_env {declName : Name} {mctx : Meta.Context}
    {mref : ST.Ref IO.RealWorld Meta.State} {cctx : Core.Context}
    {cref : ST.Ref IO.RealWorld Core.State} {wst wst' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Design} {value : Lean.Expr}
    {bs : List (Name × MixedGateBinder)}
    {dpos : Nat} {aw dw kb kv : Nat} {vw : Nat → Nat} {bpos vpos : Nat → Nat}
    {eWA : Term (.bits aw)} {eWD : Term (.bits dw)}
    {eWEN : Term .bool} {eRA : Term (.bits aw)}
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref wst
      (m, design) wst')
    (env : EnvDefines mctx mref cctx cref declName value)
    (old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none)
    (peel : mixedGatePeel value = some (bs, memoryE (inputExpr bs.length dpos) aw dw
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eWA)
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eWD)
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eWEN)
      (quote (inputExpr bs.length dpos) (fun j => inputExpr bs.length (bpos j)) (fun j => inputExpr bs.length (vpos j)) eRA)))
    (hdp : dpos < bs.length) (haw : 0 < aw) (hdw : 0 < dw)
    (hWA : eWA.WF kb kv vw) (hWD : eWD.WF kb kv vw)
    (hWEN : eWEN.WF kb kv vw) (hRA : eRA.WF kb kv vw)
    (hb : ∀ j, j < kb → ∃ name, bs[bpos j]? = some (name, .bool))
    (hvp : ∀ j, j < kv → ∃ name, bs[vpos j]? = some (name, .bits (vw j))) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = bs.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (nm rdW : String), rdW ≠ "out" ∧
      ∀ {D : Sparkle.Core.Domain.DomainConfig}
        (boolsS : Nat → Sparkle.Core.Signal.Signal D Bool)
        (bitsS : (j : Nat) → (n : Nat) → Sparkle.Core.Signal.Signal D (BitVec n))
        (mems0 : MEnv) (k : Nat)
        (seed : Nat → (String → Nat) → Env) (st0 : String → Nat)
        (S : Nat → Nat) (M : Nat → MEnv),
      (∀ t stv, SourceInputs declName bs ids cache
          (fun i => (boolsS i).val (k - 1 - t)) (fun i n => (bitsS i n).val (k - 1 - t))
          (seed t stv) ∧ seed t stv rdW = stv rdW) →
      S 0 = st0 rdW → M 0 = mems0 →
      (∀ j, j + 1 ≤ k → S (j + 1) = mask dw (M j nm (mask aw
        (eval (fun i => (boolsS (bpos i)).val j) (fun i n => (bitsS (vpos i) n).val j)
          eRA).toNat))) →
      (∀ j, j + 1 ≤ k → M (j + 1) =
        if eval (fun i => (boolsS (bpos i)).val j) (fun i n => (bitsS (vpos i) n).val j)
            eWEN then
          (fun n i => if n = nm ∧ i = mask aw
              (eval (fun i => (boolsS (bpos i)).val j)
                (fun i n => (bitsS (vpos i) n).val j) eWA).toNat
            then mask dw (eval (fun i => (boolsS (bpos i)).val j)
              (fun i n => (bitsS (vpos i) n).val j) eWD).toNat
            else M j n i)
        else M j) →
      ∃ envs, runModule (weOf m) m.body seed k st0 mems0 = some envs ∧
        envs.length = k ∧
        ∀ j (hj : j < envs.length), (envs[j]'hj) "out" = S j := by
  obtain ⟨ids, nd, len, cache, nm, rdW, rdNe, H⟩ :=
    memoryCone_step_of_env hr env old peel hdp haw hdw hWA hWD hWEN hRA hb hvp
  refine ⟨ids, nd, len, cache, nm, rdW, rdNe, ?_⟩
  intro D boolsS bitsS mems0 k seed st0 S M hseed hS0 hM0 hSs hMs
  refine Tools.ShippingMemorySoundness.trace_of_cycles_memArr
    (L := fun t mems => mask dw (mems nm (mask aw
      (eval (fun i => (boolsS (bpos i)).val (k - 1 - t))
        (fun i n => (bitsS (vpos i) n).val (k - 1 - t)) eRA).toNat)))
    (G := fun t mems =>
      if eval (fun i => (boolsS (bpos i)).val (k - 1 - t))
          (fun i n => (bitsS (vpos i) n).val (k - 1 - t)) eWEN then
        (fun n i => if n = nm ∧ i = mask aw
            (eval (fun i => (boolsS (bpos i)).val (k - 1 - t))
              (fun i n => (bitsS (vpos i) n).val (k - 1 - t)) eWA).toNat
          then mask dw (eval (fun i => (boolsS (bpos i)).val (k - 1 - t))
            (fun i n => (bitsS (vpos i) n).val (k - 1 - t)) eWD).toNat
          else mems n i)
      else mems)
    (fun t stv mems => ?_) k st0 mems0 S M hS0 hM0 ?_ ?_
  · obtain ⟨envF, hstep, hout⟩ := H (fun i => (boolsS i).val (k - 1 - t))
      (fun i n => (bitsS i n).val (k - 1 - t)) (seed t stv) mems (hseed t stv).1
    exact ⟨envF, hstep, hout.trans (hseed t stv).2⟩
  · intro j hj
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    simp only [hidx]
    exact hSs j hj
  · intro j hj
    have hidx : k - 1 - (k - 1 - j) = j := by omega
    simp only [hidx]
    exact hMs j hj

end Tools.ShippingMemoryEntrySoundness
