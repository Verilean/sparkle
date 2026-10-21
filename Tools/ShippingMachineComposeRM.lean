import Tools.ShippingMachineComposeRA
import Tools.ShippingServedRealATrace
-- BUILT (unit SR2d, par/u-sr2d): rm1/rm4 exit 0 (via Tests.Compiler.ComposedCallerMixEntryTest); co-import co1 exit 0. No `sorry`, no `axiom`, no `native_decide`, no new law / field.

/-! # Unit SR2d: the data-ext trace head on the new boundary

`machine_traceL_of_data_extRM` is `Tools.ShippingMachineComposeR.machine_traceL_of_data_extRA` with the
trace discharged by `Tools.ShippingServedRealATrace.machine_trace_lets_of_streamBRA_main` at the core run
`hr`, `MachineDefines`, `MachineClosesAtA`, start world `JQ O.quiet 0 w`. Boundary premises: `O`, `hA`,
`T : RefLawsATele` (a separate assumption family; it supplies `BodyStepC`/`htr`). The conclusion is a
trace WITH child history (`ServedRealA`), not composed-parent semantics. -/
namespace Tools.ShippingMachineComposeRM
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST
open Tools.ShippingMachineTraceX (MachineTraceLBX)
open Tools.ShippingChildInvA Tools.ShippingChildFresh Tools.ShippingChildVCA Tools.ShippingChildRunAKids
open Tools.ShippingServedRealA Tools.ShippingServedRealATrace

/-- `machine_traceL_of_data_ext` carrying `ServedRealA O`, the trace derived from the core run (no `ChildBnd`). -/
theorem machine_traceL_of_data_extRM {declName : Name} (d : MachineData) {ι : Type}
    (dom : ι → DomainConfig) [Inhabited (HList (tys d.ss))] {ρ : ι → Type}
    (inits : HList (tys d.ss))
    (body : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      RegList (dom i) (HList (tys d.ss)) (Circuit.SigList (dom i) (tys d.ss)) (tys d.ss) →
      Circuit (dom i) (Circuit.SigList (dom i) (tys d.ss)) (ρ i))
    (obsR : (i : ι) → ρ i → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      Signal (dom i) (HList (tys d.ss)) → (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ok : d.ok = true)
    (hbody : d.shape.body = quote d.dom
      (fun j => inputExpr d.shape.binders.length (d.bpos j))
      (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed)
    (hinit : d.initOk inits = true)
    (writes : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      valsAt (tys d.ss) (body i bools bits
          (mkRegList S (tys d.ss) (fun s => s) (fun f => f)) (mkHolds (tys d.ss) S)).snd t =
        evalTerms
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S) t
            (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S) t
            (S.val t)).v (d.vpos j) w) d.nexts)
    (hres : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t : Nat),
      (obsR i (body i bools bits (mkRegList S (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) S)).fst).map (fun f => f t) =
        d.outs.map fun o => enc o.1 (eval
          (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S) t
            (S.val t)).b (d.bpos j))
          (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S) t
            (S.val t)).v (d.vpos j) w) o.2))
    (hsrc : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)),
      src i bools bits = obsR i
        (body i bools bits
          (mkRegList (stateLoop inits (body i bools bits)) (tys d.ss) (fun s => s) (fun f => f))
          (mkHolds (tys d.ss) (stateLoop inits (body i bools bits)))).fst)
    (hext : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (S : Signal (dom i) (HList (tys d.ss))) (t p w : Nat),
      (ext i bools bits S p w).val t = (ext i bools bits ⟨fun _ => S.val t⟩ p w).val t)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
    {m : Sparkle.IR.AST.Module} {design : Sparkle.IR.AST.Design}
    (O : RefLawsAOps MkRefd mref cref) (hA : AdmCtx O.quiet mctx cctx)
    (T : RefLawsATele O.quiet mref cref)
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineClosesAtA (mref := mref) (cref := cref) O mctx cctx declName d.shape)
    (hw : JQ O.quiet 0 w) :
    MachineTraceLBX (ServedRealA O declName d.shape m design) declName d m design dom src
      (fun i bools bits => ext i bools bits (stateLoop inits (body i bools bits)))
      (fun _ bools _ => bools)
      (letObs d dom inits body ext) := by
  refine machine_trace_lets_of_streamBRA_main O hA T d dom inits src (letObs d dom inits body ext) ok hbody
    hinit _ (fun _ bools _ => bools) ?_ hr entry closes hw (Or.inl rfl)
  intro i bools bits
  have hloop := stateLoop_stream inits (body i bools bits)
    (fun t x => evalTerms
      (fun j => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools
        (ext i bools bits ⟨fun _ => x⟩) t x).b (d.bpos j))
      (fun j w => (typedVal d.nIn d.bpos d.vpos d.ss d.ls bools
        (ext i bools bits ⟨fun _ => x⟩) t x).v (d.vpos j) w)
      d.nexts) (by
      intro S t
      rw [writes i bools bits S t,
        typedVal_congr d.nIn d.bpos d.vpos d.ss d.ls bools (ext i bools bits S)
          (ext i bools bits ⟨fun _ => S.val t⟩) t (S.val t) (fun p w => hext i bools bits S t p w)])
  refine ⟨fun t => (stateLoop inits (body i bools bits)).val t, hloop.1, ?_, ?_, ?_⟩
  · intro t
    show (stateLoop inits (body i bools bits)).val (t + 1) = _
    rw [hloop.2 t]
    rw [typedVal_congr d.nIn d.bpos d.vpos d.ss d.ls bools
      (ext i bools bits (stateLoop inits (body i bools bits)))
      (ext i bools bits ⟨fun _ => (stateLoop inits (body i bools bits)).val t⟩) t _
      (fun p w => hext i bools bits (stateLoop inits (body i bools bits)) t p w)]
  · intro j
    rw [hsrc i bools bits]
    exact hres i bools bits (stateLoop inits (body i bools bits)) j
  · intro j q g l hg hl
    simp only [letObs, List.getElem?_map, hl, Option.map_some, Option.some.injEq] at hg
    subst hg
    rfl

end Tools.ShippingMachineComposeRM
