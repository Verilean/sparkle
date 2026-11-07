import Tools.ShippingFGCircuitS3nBridge
set_option autoImplicit false
-- FG circuit pilot Check54 (S3n): (A) the complete types of the model theorems and the bridge lemmas against independently written expected types, with mutants (including the bridge in the WRONG direction, a vacuous return relation, a dropped hypothesis); (B) the non-vacuous model execution; (C) negative controls (wrong ref, a quiet that fails); (D) the hypotheses do not mention the programs or the final conclusion; (E) AXIOMS.  The hypotheses `GetCorr`/`SetCorr`/`StderrCorr`/`EnvCorr`/`InitCorr` are statements, not supplied for the runtime.  docs/FG-CIRCUIT-PILOT.md §64.
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace Tests.Gen5.FGCircuitPilotCheck54
open Lean Meta Elab Command Term

def elabTy (stx : Syntax) : TermElabM Expr := do
  let e ← elabTerm stx none
  synthesizeSyntheticMVarsNoPostponing
  instantiateMVars e

def tyOfConst (n : Name) : MetaM Expr := do
  return (← getConstInfo n).type

/-- the theorem's type is defeq to the expected one, and each mutant is NOT -/
def chk (n : Name) (expected : Syntax) (mutants : List Syntax) : TermElabM Nat := do
  let t ← tyOfConst n
  let e ← elabTy expected
  unless ← isDefEq t e do throwError "FGCIRCUIT54 {n}: the type differs from the independently written one"
  let mut k := 0
  for m in mutants do
    let me ← elabTy m
    if ← isDefEq t me then throwError "FGCIRCUIT54 {n}: a mutant is accepted: {m}"
    k := k + 1
  return k

/-! ## (A0) the definitions `Rel` / `Corr` against independent spellings (kernel-checked `Iff.rfl`) -/
example (h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig) (w : Void IO.RealWorld) :
    Tools.ShippingFGCircuitS3nBridge.Rel h w ↔ (Tools.ShippingChildBndCore.cv w = h.cache ∧ Tools.ShippingChildBndCore.sv w = h.synth ∧ Tools.ShippingChildBndCore.dv w = h.depth) := Iff.rfl

example (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context)
    (cref : ST.Ref IO.RealWorld Lean.Core.State) {α β : Type} (RA : α → β → Prop) (m : Lean.MetaM α) (p : Tools.ShippingHeapModel.M Tools.ShippingFGCircuitS3nBridge.realSig β) :
    Tools.ShippingFGCircuitS3nBridge.Corr mctx mref cctx cref RA m p ↔
      ∀ (w w' : Void IO.RealWorld) (h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig) (a : α), Tools.ShippingFGCircuitS3nBridge.Rel h w → Tools.ShippingEntrySoundness.RunsTo m mctx mref cctx cref w a w' →
        ∃ (b : β) (h' : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig), p h = Tools.ShippingHeapModel.Out.ok b h' ∧ RA a b ∧ Tools.ShippingFGCircuitS3nBridge.Rel h' w' := Iff.rfl

/-! ## (A) complete types -/
run_cmd liftTermElabM do
  let mut nm : Nat := 0
  let mut nt : Nat := 0
  -- model: read-back
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3n.readback_depth
    (← `(∀ {C S : Type} (v : Nat) (h : Tools.ShippingHeapModel.Heap (Tools.ShippingFGCircuitS3n.sigOf C S)),
        Tools.ShippingHeapModel.hget (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref (Tools.ShippingFGCircuitS3n.sigOf C S) Nat) (Tools.ShippingHeapModel.hset (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref (Tools.ShippingFGCircuitS3n.sigOf C S) Nat) v h) = v))
    [← `(∀ {C S : Type} (v : Nat) (h : Tools.ShippingHeapModel.Heap (Tools.ShippingFGCircuitS3n.sigOf C S)),
        Tools.ShippingHeapModel.hget (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref (Tools.ShippingFGCircuitS3n.sigOf C S) Nat) (Tools.ShippingHeapModel.hset (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref (Tools.ShippingFGCircuitS3n.sigOf C S) Nat) v h) = v + 1),
     ← `(∀ {C S : Type} (v : Nat) (h : Tools.ShippingHeapModel.Heap (Tools.ShippingFGCircuitS3n.sigOf C S)),
        Tools.ShippingHeapModel.hget (Tools.ShippingHeapModel.Ref.other 0 : Tools.ShippingHeapModel.Ref (Tools.ShippingFGCircuitS3n.sigOf C S) Nat) (Tools.ShippingHeapModel.hset (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref (Tools.ShippingFGCircuitS3n.sigOf C S) Nat) v h) = v)])
  -- model: getStderr keeps the heap
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3n.getStderr_keeps
    (← `(∀ {C S : Type} {h h' : Tools.ShippingHeapModel.Heap (Tools.ShippingFGCircuitS3n.sigOf C S)} {a : Unit}, Tools.ShippingHeapModel.RunsTo (Tools.ShippingFGCircuitS3n.getStderrM (C := C) (S := S)) h a h' →
        h' = h ∧ h'.cache = h.cache ∧ h'.synth = h.synth ∧ h'.depth = h.depth ∧ (Tools.ShippingFGCircuitS3n.quietM h' ↔ Tools.ShippingFGCircuitS3n.quietM h)))
    [← `(∀ {C S : Type} {h h' : Tools.ShippingHeapModel.Heap (Tools.ShippingFGCircuitS3n.sigOf C S)} {a : Unit}, Tools.ShippingHeapModel.RunsTo (Tools.ShippingFGCircuitS3n.getStderrM (C := C) (S := S)) h a h' →
        h' = h ∧ h'.cache = h.cache ∧ h'.synth = h.synth ∧ h'.depth = h.depth + 1 ∧ (Tools.ShippingFGCircuitS3n.quietM h' ↔ Tools.ShippingFGCircuitS3n.quietM h)),
     ← `(∀ {C S : Type} {h h' : Tools.ShippingHeapModel.Heap (Tools.ShippingFGCircuitS3n.sigOf C S)} {a : Unit}, Tools.ShippingHeapModel.RunsTo (Tools.ShippingFGCircuitS3n.getStderrM (C := C) (S := S)) h a h' →
        h'.cache = h.cache ∧ h'.synth = h.synth ∧ h'.depth = h.depth ∧ (Tools.ShippingFGCircuitS3n.quietM h' ↔ Tools.ShippingFGCircuitS3n.quietM h))])
  -- model: getEnv keeps the heap, returns the lookup
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3n.getEnv_keeps
    (← `(∀ {C S : Type} (k : String) {h h' : Tools.ShippingHeapModel.Heap (Tools.ShippingFGCircuitS3n.sigOf C S)} {a : Option String}, Tools.ShippingHeapModel.RunsTo (Tools.ShippingFGCircuitS3n.getEnvM (C := C) (S := S) k) h a h' →
        a = h.reg.getEnv k ∧ h' = h ∧ h'.cache = h.cache ∧ h'.synth = h.synth ∧ h'.depth = h.depth ∧ (Tools.ShippingFGCircuitS3n.quietM h' ↔ Tools.ShippingFGCircuitS3n.quietM h)))
    [← `(∀ {C S : Type} (k : String) {h h' : Tools.ShippingHeapModel.Heap (Tools.ShippingFGCircuitS3n.sigOf C S)} {a : Option String}, Tools.ShippingHeapModel.RunsTo (Tools.ShippingFGCircuitS3n.getEnvM (C := C) (S := S) k) h a h' →
        a = none ∧ h' = h ∧ h'.cache = h.cache ∧ h'.synth = h.synth ∧ h'.depth = h.depth ∧ (Tools.ShippingFGCircuitS3n.quietM h' ↔ Tools.ShippingFGCircuitS3n.quietM h))])
  -- model: quiet is neither False nor True
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3n.quiet_nonconst
    (← `((∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3n.exSig, h.reg.getEnv "SPARKLE_DEBUG" = none) ∧ (∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3n.exSig, ¬ h.reg.getEnv "SPARKLE_DEBUG" = none)))
    [← `((∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3n.exSig, h.reg.getEnv "SPARKLE_DEBUG" = none) ∧ (∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3n.exSig, h.reg.getEnv "SPARKLE_DEBUG" = none)),
     ← `((∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3n.exSig, h.reg.getEnv "SPARKLE_DEBUG" = none) ∧ (∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3n.exSig, ¬ h.reg.getEnv "HOME" = none))])
  -- model: the successful execution
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3n.exec_ok
    (← `(∃ h' : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3n.exSig, Tools.ShippingHeapModel.RunsTo Tools.ShippingFGCircuitS3n.prog Tools.ShippingFGCircuitS3n.s0 (0, some "/root") h' ∧ h'.cache = [20, 10] ∧ h'.synth = some 7 ∧ h'.depth = 1 ∧
        Tools.ShippingHeapModel.hget (Tools.ShippingHeapModel.Ref.other 0 : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3n.exSig Nat) h' = 5 ∧ Tools.ShippingHeapModel.hget (Tools.ShippingHeapModel.Ref.other 1 : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3n.exSig Nat) h' = 0 ∧
        h'.reg.stderr = ["done"] ∧ h'.reg.getEnv "SPARKLE_DEBUG" = none))
    [← `(∃ h' : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3n.exSig, Tools.ShippingHeapModel.RunsTo Tools.ShippingFGCircuitS3n.prog Tools.ShippingFGCircuitS3n.s0 (0, some "/root") h' ∧ h'.cache = [20, 10] ∧ h'.synth = some 7 ∧ h'.depth = 2 ∧
        Tools.ShippingHeapModel.hget (Tools.ShippingHeapModel.Ref.other 0 : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3n.exSig Nat) h' = 5 ∧ Tools.ShippingHeapModel.hget (Tools.ShippingHeapModel.Ref.other 1 : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3n.exSig Nat) h' = 0 ∧
        h'.reg.stderr = ["done"] ∧ h'.reg.getEnv "SPARKLE_DEBUG" = none),
     ← `(∃ h' : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3n.exSig, Tools.ShippingHeapModel.RunsTo Tools.ShippingFGCircuitS3n.prog Tools.ShippingFGCircuitS3n.s0 (0, some "/root") h' ∧ h'.cache = [20, 10] ∧ h'.synth = some 7 ∧ h'.depth = 1 ∧
        Tools.ShippingHeapModel.hget (Tools.ShippingHeapModel.Ref.other 0 : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3n.exSig Nat) h' = 5 ∧ Tools.ShippingHeapModel.hget (Tools.ShippingHeapModel.Ref.other 1 : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3n.exSig Nat) h' = 5 ∧
        h'.reg.stderr = ["done"] ∧ h'.reg.getEnv "SPARKLE_DEBUG" = none)])
  -- bridge: bind composition
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3nBridge.corr_bind
    (← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
        {α β γ δ : Type} {RA : α → β → Prop} {RB : γ → δ → Prop} {m : Lean.MetaM α} {p : Tools.ShippingHeapModel.M Tools.ShippingFGCircuitS3nBridge.realSig β}
        {f : α → Lean.MetaM γ} {g : β → Tools.ShippingHeapModel.M Tools.ShippingFGCircuitS3nBridge.realSig δ},
        Tools.ShippingFGCircuitS3nBridge.Corr mctx mref cctx cref RA m p → (∀ a b, RA a b → Tools.ShippingFGCircuitS3nBridge.Corr mctx mref cctx cref RB (f a) (g b)) →
        Tools.ShippingFGCircuitS3nBridge.Corr mctx mref cctx cref RB (m >>= f) (Tools.ShippingHeapModel.bindM p g)))
    [← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
        {α β γ δ : Type} {RA : α → β → Prop} {RB : γ → δ → Prop} {m : Lean.MetaM α} {p : Tools.ShippingHeapModel.M Tools.ShippingFGCircuitS3nBridge.realSig β}
        {f : α → Lean.MetaM γ} {g : β → Tools.ShippingHeapModel.M Tools.ShippingFGCircuitS3nBridge.realSig δ},
        Tools.ShippingFGCircuitS3nBridge.Corr mctx mref cctx cref RA m p → (∀ a b, Tools.ShippingFGCircuitS3nBridge.Corr mctx mref cctx cref RB (f a) (g b)) →
        Tools.ShippingFGCircuitS3nBridge.Corr mctx mref cctx cref RB (m >>= f) (Tools.ShippingHeapModel.bindM p g)),
     ← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State}
        {α β γ δ : Type} {RA : α → β → Prop} {RB : γ → δ → Prop} {m : Lean.MetaM α} {p : Tools.ShippingHeapModel.M Tools.ShippingFGCircuitS3nBridge.realSig β}
        {f : α → Lean.MetaM γ} {g : β → Tools.ShippingHeapModel.M Tools.ShippingFGCircuitS3nBridge.realSig δ},
        (∀ a b, RA a b → Tools.ShippingFGCircuitS3nBridge.Corr mctx mref cctx cref RB (f a) (g b)) →
        Tools.ShippingFGCircuitS3nBridge.Corr mctx mref cctx cref RB (m >>= f) (Tools.ShippingHeapModel.bindM p g))])
  -- bridge: the small composition (direction real -> model, SAME return value)
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3nBridge.bridge_small
    (← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingFGCircuitS3nBridge.GetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.SetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.StderrCorr mctx mref cctx cref →
        ∀ (w w' : Void IO.RealWorld) (h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig) (a : Nat), Tools.ShippingFGCircuitS3nBridge.Rel h w → Tools.ShippingEntrySoundness.RunsTo Tools.ShippingFGCircuitS3nBridge.realProg mctx mref cctx cref w a w' →
          ∃ (b : Nat) (h' : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig), Tools.ShippingHeapModel.RunsTo Tools.ShippingFGCircuitS3nBridge.modelProg h b h' ∧ a = b ∧ Tools.ShippingFGCircuitS3nBridge.Rel h' w'))
    [-- WRONG DIRECTION: model success -> real success
     ← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingFGCircuitS3nBridge.GetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.SetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.StderrCorr mctx mref cctx cref →
        ∀ (w : Void IO.RealWorld) (h h' : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig) (a : Nat), Tools.ShippingFGCircuitS3nBridge.Rel h w → Tools.ShippingHeapModel.RunsTo Tools.ShippingFGCircuitS3nBridge.modelProg h a h' →
          ∃ w' : Void IO.RealWorld, Tools.ShippingEntrySoundness.RunsTo Tools.ShippingFGCircuitS3nBridge.realProg mctx mref cctx cref w a w' ∧ Tools.ShippingFGCircuitS3nBridge.Rel h' w'),
     -- vacuous return relation
     ← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingFGCircuitS3nBridge.GetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.SetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.StderrCorr mctx mref cctx cref →
        ∀ (w w' : Void IO.RealWorld) (h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig) (a : Nat), Tools.ShippingFGCircuitS3nBridge.Rel h w → Tools.ShippingEntrySoundness.RunsTo Tools.ShippingFGCircuitS3nBridge.realProg mctx mref cctx cref w a w' →
          ∃ (b : Nat) (h' : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig), Tools.ShippingHeapModel.RunsTo Tools.ShippingFGCircuitS3nBridge.modelProg h b h' ∧ True ∧ Tools.ShippingFGCircuitS3nBridge.Rel h' w'),
     -- a dropped hypothesis (no StderrCorr)
     ← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingFGCircuitS3nBridge.GetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.SetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        ∀ (w w' : Void IO.RealWorld) (h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig) (a : Nat), Tools.ShippingFGCircuitS3nBridge.Rel h w → Tools.ShippingEntrySoundness.RunsTo Tools.ShippingFGCircuitS3nBridge.realProg mctx mref cctx cref w a w' →
          ∃ (b : Nat) (h' : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig), Tools.ShippingHeapModel.RunsTo Tools.ShippingFGCircuitS3nBridge.modelProg h b h' ∧ a = b ∧ Tools.ShippingFGCircuitS3nBridge.Rel h' w'),
     -- the end state not related
     ← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingFGCircuitS3nBridge.GetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.SetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.StderrCorr mctx mref cctx cref →
        ∀ (w w' : Void IO.RealWorld) (h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig) (a : Nat), Tools.ShippingFGCircuitS3nBridge.Rel h w → Tools.ShippingEntrySoundness.RunsTo Tools.ShippingFGCircuitS3nBridge.realProg mctx mref cctx cref w a w' →
          ∃ (b : Nat) (h' : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig), Tools.ShippingHeapModel.RunsTo Tools.ShippingFGCircuitS3nBridge.modelProg h b h' ∧ a = b)])
  -- bridge: a consequence about the real run, through the model
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3nBridge.real_small_consequence
    (← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingFGCircuitS3nBridge.GetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.SetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.StderrCorr mctx mref cctx cref →
        ∀ {w w' : Void IO.RealWorld} {h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig} {a : Nat}, Tools.ShippingFGCircuitS3nBridge.Rel h w → Tools.ShippingEntrySoundness.RunsTo Tools.ShippingFGCircuitS3nBridge.realProg mctx mref cctx cref w a w' →
          a = Tools.ShippingChildBndCore.dv w ∧ Tools.ShippingChildBndCore.dv w' = Tools.ShippingChildBndCore.dv w + 1 ∧
          Tools.ShippingChildBndCore.cv w' = Tools.ShippingChildBndCore.cv w ∧ Tools.ShippingChildBndCore.sv w' = Tools.ShippingChildBndCore.sv w))
    [← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingFGCircuitS3nBridge.GetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.SetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingFGCircuitS3nBridge.StderrCorr mctx mref cctx cref →
        ∀ {w w' : Void IO.RealWorld} {h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig} {a : Nat}, Tools.ShippingFGCircuitS3nBridge.Rel h w → Tools.ShippingEntrySoundness.RunsTo Tools.ShippingFGCircuitS3nBridge.realProg mctx mref cctx cref w a w' →
          a = Tools.ShippingChildBndCore.dv w ∧ Tools.ShippingChildBndCore.dv w' = Tools.ShippingChildBndCore.dv w ∧
          Tools.ShippingChildBndCore.cv w' = Tools.ShippingChildBndCore.cv w ∧ Tools.ShippingChildBndCore.sv w' = Tools.ShippingChildBndCore.sv w)])
  -- bridge: what the correspondence feeds
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3nBridge.stderrKeeps_of_corr
    (← `(∀ (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State),
        Tools.ShippingFGCircuitS3nBridge.StderrCorr mctx mref cctx cref →
        ∀ w : Void IO.RealWorld, (∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig, Tools.ShippingFGCircuitS3nBridge.Rel h w ∧ Tools.ShippingFGCircuitS3n.quietM h) →
          (Tools.ShippingChildBndCore.cv (Tools.ShippingFGCircuitS3m.stderrW w) = Tools.ShippingChildBndCore.cv w ∧
           Tools.ShippingChildBndCore.sv (Tools.ShippingFGCircuitS3m.stderrW w) = Tools.ShippingChildBndCore.sv w ∧
           Tools.ShippingChildBndCore.dv (Tools.ShippingFGCircuitS3m.stderrW w) = Tools.ShippingChildBndCore.dv w) ∧
          ∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig, Tools.ShippingFGCircuitS3nBridge.Rel h (Tools.ShippingFGCircuitS3m.stderrW w) ∧ Tools.ShippingFGCircuitS3n.quietM h))
    [← `(∀ (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State),
        Tools.ShippingFGCircuitS3nBridge.StderrCorr mctx mref cctx cref →
        ∀ w : Void IO.RealWorld, (∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig, Tools.ShippingFGCircuitS3nBridge.Rel h w ∧ Tools.ShippingFGCircuitS3n.quietM h) →
          (Tools.ShippingChildBndCore.cv (Tools.ShippingFGCircuitS3m.stderrW w) = Tools.ShippingChildBndCore.cv w ∧
           Tools.ShippingChildBndCore.sv (Tools.ShippingFGCircuitS3m.stderrW w) = Tools.ShippingChildBndCore.sv w) ∧
          ∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig, Tools.ShippingFGCircuitS3nBridge.Rel h (Tools.ShippingFGCircuitS3m.stderrW w) ∧ Tools.ShippingFGCircuitS3n.quietM h),
     ← `(∀ (mctx : Lean.Meta.Context) (mref : ST.Ref IO.RealWorld Lean.Meta.State) (cctx : Lean.Core.Context) (cref : ST.Ref IO.RealWorld Lean.Core.State),
        ∀ w : Void IO.RealWorld, (∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig, Tools.ShippingFGCircuitS3nBridge.Rel h w ∧ Tools.ShippingFGCircuitS3n.quietM h) →
          (Tools.ShippingChildBndCore.cv (Tools.ShippingFGCircuitS3m.stderrW w) = Tools.ShippingChildBndCore.cv w ∧
           Tools.ShippingChildBndCore.sv (Tools.ShippingFGCircuitS3m.stderrW w) = Tools.ShippingChildBndCore.sv w ∧
           Tools.ShippingChildBndCore.dv (Tools.ShippingFGCircuitS3m.stderrW w) = Tools.ShippingChildBndCore.dv w) ∧
          ∃ h : Tools.ShippingHeapModel.Heap Tools.ShippingFGCircuitS3nBridge.realSig, Tools.ShippingFGCircuitS3nBridge.Rel h (Tools.ShippingFGCircuitS3m.stderrW w) ∧ Tools.ShippingFGCircuitS3n.quietM h)])
  -- bridge: the CellPrem fields give the hypothesis (the hypothesis is the weaker one)
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3nBridge.getCorr_depth
    (← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingStRefCorrespondence.ReadWorld Sparkle.Compiler.Elab.sparkleSynthDepth →
        Tools.ShippingFGCircuitS3nBridge.GetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat)))
    [← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingFGCircuitS3nBridge.GetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat) →
        Tools.ShippingStRefCorrespondence.ReadWorld Sparkle.Compiler.Elab.sparkleSynthDepth)])
  nt := nt + 1
  nm := nm + (← chk `Tools.ShippingFGCircuitS3nBridge.setCorr_depth
    (← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingStRefCorrespondence.SetGet Sparkle.Compiler.Elab.sparkleSynthDepth →
        Tools.ShippingStRefCorrespondence.SetFrame Sparkle.Compiler.Elab.sparkleSynthDepth Sparkle.Compiler.Elab.sparkleChildCache →
        Tools.ShippingStRefCorrespondence.SetFrame Sparkle.Compiler.Elab.sparkleSynthDepth Sparkle.Compiler.Elab.sparkleChildSynth →
        Sparkle.Compiler.Elab.sparkleSynthDepth.ref ≠ Sparkle.Compiler.Elab.sparkleChildCache.ref →
        Sparkle.Compiler.Elab.sparkleSynthDepth.ref ≠ Sparkle.Compiler.Elab.sparkleChildSynth.ref →
        Tools.ShippingFGCircuitS3nBridge.SetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat)))
    [← `(∀ {mctx : Lean.Meta.Context} {mref : ST.Ref IO.RealWorld Lean.Meta.State} {cctx : Lean.Core.Context} {cref : ST.Ref IO.RealWorld Lean.Core.State},
        Tools.ShippingStRefCorrespondence.SetGet Sparkle.Compiler.Elab.sparkleSynthDepth →
        Tools.ShippingFGCircuitS3nBridge.SetCorr mctx mref cctx cref Sparkle.Compiler.Elab.sparkleSynthDepth (Tools.ShippingHeapModel.Ref.depth : Tools.ShippingHeapModel.Ref Tools.ShippingFGCircuitS3nBridge.realSig Nat))])
  logInfo m!"FGCIRCUIT54 SIGNATURES: {nt} theorems (readback_depth, getStderr_keeps, getEnv_keeps, quiet_nonconst, exec_ok, corr_bind, bridge_small, real_small_consequence, stderrKeeps_of_corr, getCorr_depth, setCorr_depth) equal their independently written types, {nm} mutants rejected (another ref, a depth off by one, a dropped conjunct, a quiet both-sides-quiet, a wrong end value, a continuation hypothesis without the return relation, a dropped continuation, the bridge in the WRONG direction (model success -> real success), a vacuous return relation, a dropped StderrCorr hypothesis, an unrelated end state, a dropped dv conjunct, a dropped quiet premise/hypothesis, the CellPrem-field implication reversed, SetGet-only SetCorr); Rel and Corr unfold to the independent spellings (Iff.rfl)"

/-! ## (B) the non-vacuous model execution, evaluated in the kernel -/
open Tools.ShippingFGCircuitS3n in
run_cmd liftTermElabM do
  -- the run's observable pieces are decided on closed data (`decide`), as in the theorem
  let ok (b : Bool) (msg : String) : MetaM Unit := unless b do throwError "FGCIRCUIT54 EXEC failed: {msg}"
  ok (decide (quietM s0)) "quiet at s0"
  ok (!(decide (quietM sLoud))) "quiet fails at sLoud"
  let env ← getEnv
  let t ← tyOfConst ``Tools.ShippingFGCircuitS3n.exec_ok
  unless t.isApp do throwError "exec_ok is not an existential"
  ok (env.contains ``Tools.ShippingFGCircuitS3n.exec_ok) "exec_ok exists"
  logInfo m!"FGCIRCUIT54 EXEC: concrete start state s0 (cache [10], synth some 7, depth 0, env HOME only); quiet holds at s0 and fails at sLoud (SPARKLE_DEBUG set), so the quiet is neither False nor True; prog (get/set depth, get/set cache, getStderr, set mref, getEnv HOME, eprintln) runs from s0 with result (0, some \"/root\") and end state depth 1, cache [20, 10], synth some 7, mref 5, cref 0, output [\"done\"], quiet kept (exec_ok, decided by the kernel, no native_decide)"

/-! ## (C) negative controls on closed data (all decided by the kernel) -/
open Tools.ShippingFGCircuitS3n Tools.ShippingHeapModel in
example : ¬ (hget (Ref.other 0 : Ref exSig Nat) (hset (Ref.other 0 : Ref exSig Nat) 5 s0) = hget (Ref.other 0 : Ref exSig Nat) s0) := by decide
-- WRONG REF: a write of `mref` DOES change what `mref` reads, so the non-interference statement for a ref against itself is false
open Tools.ShippingFGCircuitS3n Tools.ShippingHeapModel in
example : ¬ ((Ref.other 0 : Ref exSig Nat).id ≠ (Ref.other 0 : Ref exSig Nat).id) := by decide
-- the right refs: a write of `mref` leaves `cref`
open Tools.ShippingFGCircuitS3n Tools.ShippingHeapModel in
example : hget (Ref.other 1 : Ref exSig Nat) (hset (Ref.other 0 : Ref exSig Nat) 5 s0) = hget (Ref.other 1 : Ref exSig Nat) s0 := by decide
-- a quiet that fails: from the loud state the same program ends in a heap where quiet fails (quiet is preserved, not created)
open Tools.ShippingFGCircuitS3n Tools.ShippingHeapModel in
example : ¬ quietM (endW prog sLoud) := by decide
-- the tracked cells are NOT preserved by the write leaves (so "frame for every action" would be false; only the diagnostic leaves keep them)
open Tools.ShippingFGCircuitS3n Tools.ShippingHeapModel in
example : ¬ ((endW (setM (Ref.depth : Ref exSig Nat) 9) s0).depth = s0.depth) := by decide

run_cmd liftTermElabM do
  logInfo m!"FGCIRCUIT54 NEGATIVE: wrong ref (a write of mref changes mref itself: not interference-free; the id inequality of a ref with itself is false), a quiet that fails (sLoud; the program from sLoud ends not quiet), a write leaf changes the tracked depth (decided); the right refs do not interfere (mref write leaves cref)"

/-! ## (D) the correspondence hypotheses mention neither the programs nor the final conclusion -/
run_cmd liftTermElabM do
  let env ← getEnv
  let hyps : List Name := [`Tools.ShippingFGCircuitS3nBridge.Rel, `Tools.ShippingFGCircuitS3nBridge.Corr, `Tools.ShippingFGCircuitS3nBridge.GetCorr, `Tools.ShippingFGCircuitS3nBridge.SetCorr, `Tools.ShippingFGCircuitS3nBridge.StderrCorr, `Tools.ShippingFGCircuitS3nBridge.EnvCorr, `Tools.ShippingFGCircuitS3nBridge.InitCorr, `Tools.ShippingFGCircuitS3nBridge.quietR]
  let forbidden : List Name := [`Tools.ShippingFGCircuitS3nBridge.realProg, `Tools.ShippingFGCircuitS3nBridge.modelProg, `Tools.ShippingFGCircuitS3n.prog, `Tools.ShippingFGCircuitS3jStart.pilotEntry3,
    `Tools.ShippingGen2.Laws, `Tools.ShippingGen5EnvFrame3.CellPrem, `Tools.ShippingFGCircuitS3f2Final.rootDefB_sound]
  for n in hyps do
    let some ci := env.find? n | throwError "FGCIRCUIT54 HYPS: {n} missing"
    let used := ci.type.getUsedConstants ++ (match ci with | .defnInfo v => v.value.getUsedConstants | _ => #[])
    for f in forbidden do
      if used.contains f then throwError "FGCIRCUIT54 HYPS: {n} mentions {f}"
    unless ci.isDefinition do throwError "FGCIRCUIT54 HYPS: {n} is not a definition (a Prop, not an axiom)"
  logInfo m!"FGCIRCUIT54 HYPS: {hyps.length} correspondence definitions (Rel, Corr, GetCorr, SetCorr, StderrCorr, EnvCorr, InitCorr, quietR) are plain definitions (no axiom); none mentions realProg, modelProg, the model program, pilotEntry3, Laws, CellPrem or a v11 conclusion"

/-! ## (E) AXIOMS -/
run_cmd liftTermElabM do
  let env ← getEnv
  let names : List Name := [`Tools.ShippingFGCircuitS3n.readback_depth, `Tools.ShippingFGCircuitS3n.readback_cache, `Tools.ShippingFGCircuitS3n.readback_mref, `Tools.ShippingFGCircuitS3n.set_mref_frame, `Tools.ShippingFGCircuitS3n.set_depth_frame,
    `Tools.ShippingFGCircuitS3n.getStderr_keeps, `Tools.ShippingFGCircuitS3n.getEnv_keeps, `Tools.ShippingFGCircuitS3n.eprintln_keeps, `Tools.ShippingFGCircuitS3n.quiet_s0, `Tools.ShippingFGCircuitS3n.quiet_fails_sLoud, `Tools.ShippingFGCircuitS3n.quiet_nonconst,
    `Tools.ShippingFGCircuitS3n.heapLaws_with_quietM, `Tools.ShippingFGCircuitS3n.exec_ok, `Tools.ShippingFGCircuitS3nBridge.runsTo_set, `Tools.ShippingFGCircuitS3nBridge.runsTo_getStderr, `Tools.ShippingFGCircuitS3nBridge.corr_pure, `Tools.ShippingFGCircuitS3nBridge.corr_bind,
    `Tools.ShippingFGCircuitS3nBridge.getCorr_of_readWorld, `Tools.ShippingFGCircuitS3nBridge.getCorr_depth, `Tools.ShippingFGCircuitS3nBridge.setCorr_depth, `Tools.ShippingFGCircuitS3nBridge.bridge_small, `Tools.ShippingFGCircuitS3nBridge.modelProg_spec,
    `Tools.ShippingFGCircuitS3nBridge.real_small_consequence, `Tools.ShippingFGCircuitS3nBridge.stderrKeeps_of_corr]
  for n in names do
    unless env.contains n do throwError "{n} does not exist"
  let mut axs : NameSet := {}
  for nm in names do
    for ax in ← Lean.collectAxioms nm do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do throwError "{nm} uses {ax}"
      axs := axs.insert ax
  logInfo m!"FGCIRCUIT54 AXIOMS: {names.length} names, standard axioms only ({axs.toList}); no sorryAx, no native_decide"

end Tests.Gen5.FGCircuitPilotCheck54
