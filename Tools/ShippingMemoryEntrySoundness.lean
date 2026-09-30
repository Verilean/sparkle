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
  mkApp7 (.const ``Sparkle.Core.Signal.Signal.memory [.zero]) dom (natE aw) (natE dw)
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
    {aw dw : Nat} {wai wdi weni rai : Nat}
    (hdom : (dom.isFVar || dom.isBVar) = true) (haw : 0 < aw) (hdw : 0 < dw)
    (hwa : mixedGateBVar? kinds wai = some (.bits aw))
    (hwd : mixedGateBVar? kinds wdi = some (.bits dw))
    (hwen : mixedGateBVar? kinds weni = some .bool)
    (hra : mixedGateBVar? kinds rai = some (.bits aw)) :
    unifiedMemoryRoot kinds (memoryE dom aw dw (.bvar wai) (.bvar wdi)
      (.bvar weni) (.bvar rai)) = true := by
  show ((dom.isFVar || dom.isBVar) &&
    (match canonicalNatLitValue? (natE aw), canonicalNatLitValue? (natE dw) with
     | some aw', some dw' =>
       0 < aw' && 0 < dw' &&
       mixedGateBVar? kinds wai == some (.bits aw') &&
       mixedGateBVar? kinds wdi == some (.bits dw') &&
       mixedGateBVar? kinds weni == some .bool &&
       mixedGateBVar? kinds rai == some (.bits aw')
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
    (hwa.elim fun name pos => mixedGateBVar?_pos pos)
    (hwd.elim fun name pos => mixedGateBVar?_pos pos)
    (hwen.elim fun name pos => mixedGateBVar?_pos pos)
    (hra.elim fun name pos => mixedGateBVar?_pos pos)
  simp only [mixedCertifiedShape?, List.isEmpty_nil, Bool.not_true,
    Bool.false_eq_true, if_false, peel, inputExpr, root, Bool.or_true, if_true]
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

end Tools.ShippingMemoryEntrySoundness
