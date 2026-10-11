import Tools.ShippingChildKeeps

/-! # The machine route's harness keeps the child invariant, given the translator does

`HarnessRel` (the harness `synthesizeMixedCertified`, with the entry's logger,
keeps the invariant on every outcome provided the memoised child entry does)
is PROVED here from `TranslateRel` (the same for the translator
`translateExprToWire` alone). What the harness does around the translator is
walked step by step, on every outcome:

* fresh free-variable ids, the distinctness check (a throw otherwise), the
  new translation cache;
* the binder walk (`bindMixedCertifiedInputs` / `bindInputPort`: wires and
  input ports — pure circuit-state updates and the wire-width cache);
* the leaf emission (`emitLeaves`: clock and counter reads, the logger, THE
  TRANSLATOR, the translation cache's update, the port-name check — a throw —
  the output port and its assign);
* `finishSynth` (pure, or a throw).

`TripleC` is the calculus one level up: a `CompilerM` action from every
compiler state and circuit state. -/
namespace Tools.ShippingChildInv
open Lean Meta
open Tools.ShippingEntrySoundness
open Sparkle.Compiler.Elab
open Sparkle.IR.Builder (CircuitState)

variable {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
  {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}

section Calculus
variable (mctx mref cctx cref)

/-- `Triple` for a `CompilerM` action, from every compiler and circuit state. -/
def TripleC {α : Type} (P : Void IO.RealWorld → Prop) (c : CompilerM α)
    (Q : α → Void IO.RealWorld → Prop) (R : Exception → Void IO.RealWorld → Prop) : Prop :=
  ∀ (ctx : CompilerState) (st : CircuitState),
    Triple mctx mref cctx cref P (c ctx st) (fun p => Q p.1) R

end Calculus

theorem keepsC_iff {α : Type} {I : Void IO.RealWorld → Prop} {c : CompilerM α} :
    KeepsC mctx mref cctx cref I c ↔
      TripleC mctx mref cctx cref I c (fun _ => I) (fun e w => I w ∧ OkExc e) :=
  ⟨fun h ctx st => keeps_iff.mp (h ctx st), fun h ctx st => keeps_iff.mpr (h ctx st)⟩

/-- A plain `throw`: the world is left as it is. -/
theorem Triple.throw {α : Type} {P : Void IO.RealWorld → Prop} (e : Exception)
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop} (h : ∀ w, P w → R e w) :
    Triple mctx mref cctx cref P (throw e : MetaM α) Q R := by
  intro w hw
  change match (EST.Out.error e w : EST.Out Exception IO.RealWorld α) with
    | .ok a w' => Q a w' | .error e w' => R e w'
  exact h w hw

theorem TripleC.pure {α : Type} {P : Void IO.RealWorld → Prop} {a : α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop} (h : ∀ w, P w → Q a w) :
    TripleC mctx mref cctx cref P (Pure.pure a : CompilerM α) Q R :=
  fun _ st => Triple.pure (a := (a, st)) h

theorem TripleC.bind {α β : Type} {P : Void IO.RealWorld → Prop} {c : CompilerM α}
    {f : α → CompilerM β} {Q : α → Void IO.RealWorld → Prop} {Q' : β → Void IO.RealWorld → Prop}
    {R : Exception → Void IO.RealWorld → Prop}
    (h1 : TripleC mctx mref cctx cref P c Q R)
    (h2 : ∀ a, TripleC mctx mref cctx cref (Q a) (f a) Q' R) :
    TripleC mctx mref cctx cref P (c >>= f) Q' R :=
  fun ctx st => Triple.bind (h1 ctx st) fun p => by
    obtain ⟨a, s⟩ := p
    exact h2 a ctx s

/-- A `MetaM` action lifted into `CompilerM`. -/
theorem TripleC.lift {α : Type} {P : Void IO.RealWorld → Prop} {m : MetaM α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (h : Triple mctx mref cctx cref P m Q R) :
    TripleC mctx mref cctx cref P (CompilerM.liftMetaM m) Q R :=
  fun _ st => Triple.bind h fun a => Triple.pure (a := (a, st)) fun _ hw => hw

theorem TripleC.get {P : Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop} :
    TripleC mctx mref cctx cref P (get : CompilerM CircuitState) (fun _ => P) R :=
  fun _ st => Triple.pure (a := (st, st)) fun _ hw => hw

theorem TripleC.set {P : Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (s : CircuitState) :
    TripleC mctx mref cctx cref P (set s : CompilerM PUnit) (fun _ => P) R :=
  fun _ _ => Triple.pure (a := (PUnit.unit, s)) fun _ hw => hw

theorem TripleC.getCompilerState {P : Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop} :
    TripleC mctx mref cctx cref P CompilerM.getCompilerState (fun _ => P) R :=
  fun ctx st => Triple.pure (a := (ctx, st)) fun _ hw => hw

theorem TripleC.withReader {α : Type} {P : Void IO.RealWorld → Prop} {k : CompilerM α}
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (f : CompilerState → CompilerState) (h : TripleC mctx mref cctx cref P k Q R) :
    TripleC mctx mref cctx cref P (withReader f k) Q R :=
  fun ctx st => h (f ctx) st

theorem TripleC.throw {α : Type} {P : Void IO.RealWorld → Prop} (e : Exception)
    {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop} (h : ∀ w, P w → R e w) :
    TripleC mctx mref cctx cref P (throw e : CompilerM α) Q R :=
  fun _ _ => Triple.throw e h

theorem TripleC.ite {α : Type} {c : Prop} [Decidable c] {P : Void IO.RealWorld → Prop}
    {a b : CompilerM α} {Q : α → Void IO.RealWorld → Prop} {R : Exception → Void IO.RealWorld → Prop}
    (ha : c → TripleC mctx mref cctx cref P a Q R) (hb : ¬c → TripleC mctx mref cctx cref P b Q R) :
    TripleC mctx mref cctx cref P (if c then a else b) Q R := by
  by_cases hc : c
  · rw [if_pos hc]; exact ha hc
  · rw [if_neg hc]; exact hb hc

variable (L : RefLaws mref cref)

/-! ## The circuit-state primitives -/

/-- The wire-width cache's update, lifted. -/
theorem wireWidth_tripleC (D : Nat) (f : Std.HashMap String Nat → Std.HashMap String Nat) :
    TripleC mctx mref cctx cref (J L D)
      (CompilerM.liftMetaM (ST.Ref.modify sparkleWireWidthCache f)) (fun _ => J L D) (JE L D) :=
  TripleC.lift (Triple.frame L (Framed.sideModify _ .wireWidth) D)

theorem makeWire_tripleC (D : Nat) (hint : String) (ty : Sparkle.IR.Type.HWType) (named : Bool) :
    TripleC mctx mref cctx cref (J L D) (CompilerM.makeWire hint ty named)
      (fun _ => J L D) (JE L D) := by
  unfold CompilerM.makeWire
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  dsimp only
  split
  · refine TripleC.bind (wireWidth_tripleC L D _) ?_
    intro _
    exact TripleC.pure fun _ hw => hw
  · exact TripleC.pure fun _ hw => hw

theorem addInput_tripleC (D : Nat) (name : String) (ty : Sparkle.IR.Type.HWType) :
    TripleC mctx mref cctx cref (J L D) (CompilerM.addInput name ty) (fun _ => J L D) (JE L D) := by
  unfold CompilerM.addInput
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  split
  · exact wireWidth_tripleC L D _
  · exact TripleC.pure fun _ hw => hw

theorem addOutput_tripleC (D : Nat) (name : String) (ty : Sparkle.IR.Type.HWType) :
    TripleC mctx mref cctx cref (J L D) (CompilerM.addOutput name ty) (fun _ => J L D) (JE L D) := by
  unfold CompilerM.addOutput
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  refine TripleC.bind (TripleC.set _) ?_
  intro _
  split
  · exact wireWidth_tripleC L D _
  · exact TripleC.pure fun _ hw => hw

theorem emitAssign_tripleC (D : Nat) (lhs : String) (rhs : Sparkle.IR.AST.Expr) :
    TripleC mctx mref cctx cref (J L D) (CompilerM.emitAssign lhs rhs) (fun _ => J L D) (JE L D) := by
  unfold CompilerM.emitAssign
  refine TripleC.bind TripleC.get ?_
  intro cs
  split
  exact TripleC.set _

/-! ## The binder walk -/

theorem bindInputPort_tripleC (D : Nat) {α : Type} (fv : FVarId) (bn : String)
    (ty : Sparkle.IR.Type.HWType) (k : CompilerM α)
    (hk : TripleC mctx mref cctx cref (J L D) k (fun _ => J L D) (JE L D)) :
    TripleC mctx mref cctx cref (J L D) (bindInputPort fv bn ty k) (fun _ => J L D) (JE L D) := by
  unfold bindInputPort CompilerM.withVarMapping
  refine TripleC.bind (makeWire_tripleC L D _ _ _) ?_
  intro w
  refine TripleC.bind (addInput_tripleC L D _ _) ?_
  intro _
  refine TripleC.bind TripleC.getCompilerState ?_
  intro old
  exact TripleC.withReader _ hk

theorem bindMixedCertifiedInputs_tripleC (D : Nat) {α : Type} (k : CompilerM α)
    (hk : TripleC mctx mref cctx cref (J L D) k (fun _ => J L D) (JE L D)) :
    ∀ l : List ((Name × MixedGateBinder) × FVarId),
      TripleC mctx mref cctx cref (J L D) (bindMixedCertifiedInputs k l) (fun _ => J L D) (JE L D)
  | [] => by unfold bindMixedCertifiedInputs; exact hk
  | ((_, .domain), _) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindMixedCertifiedInputs_tripleC D k hk rest
  | ((nm, .bool), id) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPort_tripleC L D _ _ _ _ (bindMixedCertifiedInputs_tripleC D k hk rest)
  | ((nm, .bits n), id) :: rest => by
    unfold bindMixedCertifiedInputs
    exact bindInputPort_tripleC L D _ _ _ _ (bindMixedCertifiedInputs_tripleC D k hk rest)

/-! ## The leaf emission -/

/-- **`emitLeaves` keeps the invariant, given the translator does**: the
clock and counter reads, the logger, the translator, the translation cache's
update, the port-name check (a throw), the output port and its assign, then
the remaining leaves. -/
theorem emitLeaves_tripleC (D : Nat) (b : Bool) (cacheRef : IO.Ref (Lean.ExprStructMap String))
    (hT : ∀ e hint top named, TripleC mctx mref cctx cref (J L D)
      (translateExprToWire e hint top named) (fun _ => J L D) (JE L D)) :
    ∀ (leaves : List (String × Lean.Expr)) (fw : Option String) (idx : Nat),
      TripleC mctx mref cctx cref (J L D)
        (emitLeaves (fun e hint top named => translateExprToWire e hint top named) cacheRef
          (profLogIO b) leaves fw idx) (fun _ => J L D) (JE L D)
  | [], fw, idx => by
    unfold emitLeaves
    exact TripleC.pure fun _ hw => hw
  | (pn, le) :: rest, fw, idx => by
    unfold emitLeaves
    have clock : TripleC mctx mref cctx cref (J L D) (CompilerM.liftMetaM (liftM IO.monoMsNow))
        (fun _ => J L D) (JE L D) := TripleC.lift (Triple.frame L Framed.monoMs D)
    have calls : TripleC mctx mref cctx cref (J L D)
        (CompilerM.liftMetaM (ST.Ref.get sparkleCallCounter)) (fun _ => J L D) (JE L D) :=
      TripleC.lift (Triple.frame L (Framed.sideGet .callCounter) D)
    have hits : TripleC mctx mref cctx cref (J L D)
        (CompilerM.liftMetaM (ST.Ref.get sparkleCacheHits)) (fun _ => J L D) (JE L D) :=
      TripleC.lift (Triple.frame L (Framed.sideGet .cacheHits) D)
    have log : ∀ msg, TripleC mctx mref cctx cref (J L D)
        (CompilerM.liftMetaM (liftM (profLogIO b msg))) (fun _ => J L D) (JE L D) :=
      fun msg => TripleC.lift (Triple.diag L (Diag.profLog b msg) D)
    refine TripleC.bind clock ?_; intro t0
    refine TripleC.bind calls ?_; intro c0
    refine TripleC.bind hits ?_; intro h0
    refine TripleC.bind (log _) ?_; intro _
    refine TripleC.bind (hT le pn false true) ?_; intro lw
    refine TripleC.bind clock ?_; intro t1
    refine TripleC.bind calls ?_; intro c1
    refine TripleC.bind hits ?_; intro h1
    refine TripleC.bind (log _) ?_; intro _
    -- the tail after the translation cache's update
    have tail : ∀ u : Unit, TripleC mctx mref cctx cref (J L D)
        ((fun (__r : Unit) => (do
          let cs ← get
          have __do_jp : Unit → CompilerM String := fun __r =>
            have wireDecl := List.find? (fun p => p.name == lw) cs.module.wires;
            have outputType :=
              match wireDecl with
              | some decl => decl.ty
              | none =>
                match List.find? (fun p => p.name == lw) cs.module.inputs with
                | some inputPort => inputPort.ty
                | none => Sparkle.IR.Type.HWType.bitVector 8;
            do
            CompilerM.addOutput pn outputType
            CompilerM.emitAssign pn (Sparkle.IR.AST.Expr.ref lw)
            emitLeaves (fun e hint top named => translateExprToWire e hint top named) cacheRef
                (profLogIO b) rest (if fw.isNone = true then some lw else fw) (idx + 1)
          if cs.usedNames.contains pn = true then do
              let __r ←
                throw
                    (Exception.error Syntax.missing
                      (toMessageData "output port name '" ++ toMessageData pn ++
                        toMessageData "' is already a name of this module"))
              __do_jp __r
            else __do_jp () : CompilerM String)) u) (fun _ => J L D) (JE L D) := by
      intro u
      dsimp only
      refine TripleC.bind TripleC.get ?_
      intro cs
      have rest' : TripleC mctx mref cctx cref (J L D)
          (do
            CompilerM.addOutput pn
              (match List.find? (fun p => p.name == lw) cs.module.wires with
              | some decl => decl.ty
              | none =>
                match List.find? (fun p => p.name == lw) cs.module.inputs with
                | some inputPort => inputPort.ty
                | none => Sparkle.IR.Type.HWType.bitVector 8)
            CompilerM.emitAssign pn (Sparkle.IR.AST.Expr.ref lw)
            emitLeaves (fun e hint top named => translateExprToWire e hint top named) cacheRef
                (profLogIO b) rest (if fw.isNone = true then some lw else fw) (idx + 1))
          (fun _ => J L D) (JE L D) := by
        refine TripleC.bind (addOutput_tripleC L D _ _) ?_
        intro _
        refine TripleC.bind (emitAssign_tripleC L D _ _) ?_
        intro _
        exact emitLeaves_tripleC D b cacheRef hT rest _ _
      refine TripleC.ite (fun _ => ?_) (fun _ => rest')
      refine TripleC.bind (Q := fun _ _ => False) (TripleC.throw _ fun _ hw => ⟨hw, by okmsg⟩) ?_
      intro _ _ _ w hf
      exact hf.elim
    dsimp only
    refine TripleC.ite (fun _ => ?_) (fun _ => tail ())
    refine TripleC.bind (TripleC.lift (Triple.frame L (Framed.exprCacheModify _ _) D)) ?_
    intro u
    exact tail u

/-! ## `finishSynth` and the harness -/

theorem finishSynth_triple (D : Nat) (declName : Name) (st : CircuitState) :
    Triple mctx mref cctx cref (J L D) (finishSynth declName [] false st)
      (fun _ => J L D) (JE L D) := by
  unfold finishSynth
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine Triple.ite (fun _ => Triple.pure fun _ hw => hw) (fun _ => Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩)

/-- **`HarnessRel` from `TranslateRel`.** -/
theorem harnessRel_of (hT : TranslateRel L) : HarnessRel L := by
  intro D hC mctx cctx b declName bs body
  rw [keeps_iff]
  unfold synthesizeMixedCertified
  refine Triple.bind (Triple.mapM _ (fun _ => Triple.frame L Framed.freshFVar D) _) ?_
  intro ids
  split
  · dsimp only
    refine Triple.bind (Triple.frame L (Framed.mkExprCache _) D) ?_
    intro cacheRef
    refine Triple.bind
      (bindMixedCertifiedInputs_tripleC L D _
        (emitLeaves_tripleC L D b cacheRef (fun e hint top named => keepsC_iff.mp (hT D hC mctx cctx e hint top named))
          _ _ _) _ _ _) ?_
    rintro ⟨_, fs⟩
    exact finishSynth_triple L D declName fs
  · exact Triple.throw _ fun _ hw => ⟨hw, by okmsg⟩

end Tools.ShippingChildInv
