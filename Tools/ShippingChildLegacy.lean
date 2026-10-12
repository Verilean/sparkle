import Tools.ShippingChildFallback

/-! # The legacy translator's handlers keep the child invariant

The block `Rec.*` is ordinary code now (`Sparkle/Compiler/Elab.lean`). Each
handler is walked here (`vc`), on every outcome, given that the translator
handed in as `tr` keeps the invariant in every context and that the memoised
child entry does: the three local recursions by induction (`normSpine` on its
fuel, `lower` on the Signal list, `getPrimitiveNameFromLambda` on the
expression), then the handlers in dependency order. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
variable (L : RefLaws mref cref) (D : Nat)
set_option maxHeartbeats 1000000

@[keeps] theorem normSpine_keeps :
    ∀ (fuel : Nat) (mctx : Meta.Context) (cctx : Core.Context) (x : Lean.Expr),
      Keeps mctx mref cctx cref (J L D) (Rec.translateExprToWireApp.normSpine x fuel)
  | 0, mctx, cctx, x => by unfold Rec.translateExprToWireApp.normSpine; vc
  | fuel + 1, mctx, cctx, x => by
    have ih := fun mctx cctx x => normSpine_keeps fuel mctx cctx x
    unfold Rec.translateExprToWireApp.normSpine
    vc

@[keeps] theorem lower_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named)) (hint : String) (named : Bool) :
    ∀ (signals : List Lean.Expr) (mctx : Meta.Context) (cctx : Core.Context) (f : Lean.Expr),
      KeepsC mctx mref cctx cref (J L D) (Rec.handleApplicative.lower tr hint named f signals)
  | [], mctx, cctx, f => by unfold Rec.handleApplicative.lower; vc
  | sig :: rest, mctx, cctx, f => by
    have ih := fun mctx cctx f => lower_keeps tr htr hint named rest mctx cctx f
    unfold Rec.handleApplicative.lower
    vc

@[keeps] theorem getPrim_keeps (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (Rec.getPrimitiveNameFromLambda e) := by
  induction e with
  | lam _ _ body _ _ ih => unfold Rec.getPrimitiveNameFromLambda; exact ih
  | _ => unfold Rec.getPrimitiveNameFromLambda; vc

@[keeps] theorem handleErrorPatterns_keeps (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleErrorPatterns e name args hint named) := by
  vc

@[keeps] theorem handleTupleProjections_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleTupleProjections tr e name args hint named) := by
  vc

@[keeps] theorem handleApplicative_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleApplicative tr e name args hint named) := by
  vc

@[keeps] theorem translateShiftAmount_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e e2 : Lean.Expr) (hint : String) :
    KeepsC mctx mref cctx cref (J L D) (Rec.translateShiftAmount tr e e2 hint) := by
  vc

@[keeps] theorem handleBitVecOps_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleBitVecOps tr e name args hint named) := by
  vc

@[keeps] theorem handleRegister_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleRegister tr e name args hint named) := by
  vc

@[keeps] theorem handleMux_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleMux tr e name args hint named) := by
  vc

@[keeps] theorem handleMemory_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleMemory tr e name args hint named) := by
  vc

@[keeps] theorem handleLoop_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleLoop tr e name args hint named) := by
  vc

@[keeps] theorem handleCircuitMonad_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleCircuitMonad tr e name args hint named) := by
  vc

/-- The snapshot of the wire-naming caches before an inline attempt: nine
reads — the context's expression cache (a run-local ref,
`LocalRefType.exprCache`) and eight global side refs (`SideRef.letWire`,
`loopWire`, `wireCanon`, `singleOut`, `subInstOut`, `wireWidth`, `fvarValue`,
`fvarZetaVisited`) — all in the frame class. None of the three tracked cells
(`sparkleChildCache`, `sparkleChildSynth`, `sparkleSynthDepth`) is read. -/
@[keeps] theorem snapshotWireCaches_keepsC :
    KeepsC mctx mref cctx cref (J L D) snapshotWireCaches := by
  vc

/-- The restore after a caught failure: nine writes of the same refs
(`Framed.localSetIO`, `Framed.sideSetIO`). None of the three tracked cells is
written. -/
@[keeps] theorem restoreWireCaches_keepsC (c : WireCaches) :
    KeepsC mctx mref cctx cref (J L D) (restoreWireCaches c) := by
  vc

/-- **The inline attempt's result**: the invariant is kept, and the exception
it returns (its second component) is none or an exception in the class — it
is one a `catch` of this run handed over (`TripleC.tryCatchQ`). This is the
provenance of what the terminal error site renders: a VALUE the calculus
tracks, not the content of a heap cell. -/
theorem tryInlineUnfold_tripleC (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (e : Lean.Expr) (hint : String) (named : Bool) :
    TripleC mctx mref cctx cref (J L D) (Rec.tryInlineUnfold tr e hint named)
      (fun a w => J L D w ∧ OkOpt a.2) (JE L D) := by
  unfold Rec.tryInlineUnfold
  refine TripleC.bind (Q := fun _ => J L D) (keepsC_iff.mp (by vc)) ?_
  intro eReduced
  refine TripleC.ite (fun _ => ?_) (fun _ => TripleC.pure fun w hw => ⟨hw, OkOpt.none⟩)
  -- the snapshot of the wire-naming caches (frame operations only)
  refine TripleC.bind (Q := fun _ => J L D)
    (keepsC_iff.mp (snapshotWireCaches_keepsC L D)) ?_
  intro saved
  refine TripleC.tryCatchQ ?_ ?_
  · refine TripleC.bind (Q := fun _ => J L D) (keepsC_iff.mp (htr _ _ _ _ _ _)) ?_
    intro w
    exact TripleC.pure fun _ hw => ⟨hw, OkOpt.none⟩
  · intro ex1 h1
    -- the restore, then the retry
    refine TripleC.bind (Q := fun _ => J L D)
      (keepsC_iff.mp (restoreWireCaches_keepsC L D saved)) ?_
    intro _
    refine TripleC.tryCatchQ ?_ ?_
    · refine TripleC.bind (Q := fun _ => J L D) (keepsC_iff.mp (by vc)) ?_
      intro eReduced2
      refine TripleC.ite (fun _ => ?_) (fun _ => TripleC.pure fun _ hw => ⟨hw, OkOpt.some h1⟩)
      refine TripleC.bind (Q := fun _ => J L D) (keepsC_iff.mp (htr _ _ _ _ _ _)) ?_
      intro w
      exact TripleC.pure fun _ hw => ⟨hw, OkOpt.none⟩
    · intro ex2 h2
      refine TripleC.bind (Q := fun _ => J L D)
        (keepsC_iff.mp (restoreWireCaches_keepsC L D saved)) ?_
      intro _
      exact TripleC.pure fun _ hw => ⟨hw, OkOpt.some h2⟩

@[keeps] theorem handleDefinitionUnfold_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (name : Name) (args : Array Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.handleDefinitionUnfold tr e name args hint named) := by
  vc

@[keeps] theorem translateExprToWireApp_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (hint : String) (named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.translateExprToWireApp tr e hint named) := by
  vc

/-- The applicative `map`'s inline mini-translator, recursive on the two
operands of an application: by induction on a bound of the expression's size,
in every context (it runs under `withLocalDecl`). -/
theorem toIR_keepsC_bound (wireS : String) (fvarId : FVarId) :
    ∀ (n : Nat) (e : Lean.Expr), sizeOf e < n →
      ∀ (mctx : Meta.Context) (cctx : Core.Context),
        KeepsC mctx mref cctx cref (J L D) (Rec.translateExprToWireImpl.toIR wireS fvarId e)
  | 0, _, h => by omega
  | n + 1, e, h => by
    intro mctx cctx
    have ih := fun e' (h' : sizeOf e' < n) (mctx : Meta.Context) (cctx : Core.Context) =>
      toIR_keepsC_bound wireS fvarId n e' h' mctx cctx
    unfold Rec.translateExprToWireImpl.toIR
    vc

@[keeps] theorem toIR_keepsC (wireS : String) (fvarId : FVarId) (e : Lean.Expr) :
    KeepsC mctx mref cctx cref (J L D) (Rec.translateExprToWireImpl.toIR wireS fvarId e) :=
  toIR_keepsC_bound L D wireS fvarId (sizeOf e + 1) e (Nat.lt_succ_self _) mctx cctx

/-- **The legacy translator's body**: its own inline arms and the handler
chain, every recursive translation through `tr`. -/
@[keeps] theorem translateExprToWireImpl_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.translateExprToWireImpl tr e hint top named) := by
  vc

/-- **Its caching shim**: the translation cache's read, the body, the cache's update. -/
@[keeps] theorem translateExprToWireCached_keeps (tr : TranslateFn)
    (htr : ∀ (mctx : Meta.Context) (cctx : Core.Context) e hint top named,
      KeepsC mctx mref cctx cref (J L D) (tr e hint top named))
    (hC : ChildKeeps L D) (e : Lean.Expr) (hint : String) (top named : Bool) :
    KeepsC mctx mref cctx cref (J L D) (Rec.translateExprToWireCached tr e hint top named) := by
  vc

/-- **`LegacyRel`, proved**: the legacy translator keeps the child invariant
whenever the memoised child entry and its recursive argument do. -/
theorem legacyRel : LegacyRel L := by
  intro D hC rec hrec mctx cctx
  exact ⟨fun e hint top named =>
      translateExprToWireCached_keeps L D (fun e h t n => rec e h t n) hrec hC e hint top named,
    fun e hint top named =>
      translateExprToWireImpl_keeps L D (fun e h t n => rec e h t n) hrec hC e hint top named⟩

/-- **`TranslateRel`, proved** — with no condition on the compiler left: the
fuel induction, the step, the certified arms, the instance arm and the legacy
translator are all walked. -/
theorem translateRel : TranslateRel L :=
  translateRel_of_legacy L (legacyRel L)

end Tools.ShippingChildInv
