import Tools.ShippingMachineTraceX
import Tools.ShippingMachineCompose
import Tools.ShippingMachineShipsHierH
import Tools.ShippingChildRun

/-! # Combinational children composed, the run boundary derived

`machine_linked_calls` takes, about each call's module, that it computes the
child's function (`ChildFn`) — for the instance that is call `k`'s statement
under the endpoint's port names (`CallStmt`); generated theorems then ask
that module to be a run of the child's entry (`GateRun` / `MachineRun`) as a
premise of the endpoint. Here that instance is DERIVED to be the module of a
run of the call's entry in the parent's contexts (`ServedReal`, on the
one-output closing by `closeInsts_serves`, under `ChildBnd`), and the
child's own theorem on that same run (`hfn`) gives `ChildFn`: the composed
theorem's per-call premise is gone (`ComposedH` with the trivial `R`). -/
namespace Tools.ShippingMachineComposeR
open Lean Sparkle.Compiler.Elab Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingUnifiedSource Tools.ShippingUnifiedMeaning
open Tools.ShippingMuxLoweringSoundness
open Tools.ShippingMachineEntry Tools.ShippingMachineRef Tools.ShippingMachineSource
open Tools.ShippingMachineDenote Tools.ShippingMachineAuto
open Tools.ShippingMachineClose (Zip₂)
open Tools.ShippingMixedEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingEntrySoundness Sparkle.IR.AST
open Tools.ShippingMachineTraceX (MachineTraceLBX ServedReal machine_trace_lets_of_streamBR
  machine_trace_lets_of_streamBRA)
open Tools.ShippingMachineCompose (ChildFn)

set_option maxHeartbeats 2000000 in
/-- `machine_traceL_of_data_ext` carrying `ServedReal` (under `ChildBnd`). -/
theorem machine_traceL_of_data_extRA {declName : Name} (d : MachineData) {ι : Type}
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
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : Tools.ShippingChildInv.MachineClosesAt mctx mref cctx cref declName d.shape)
    (hsyn : Tools.ShippingChildInv.ChildBnd mref cref w) :
    MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m design) declName d m design dom src
      (fun i bools bits => ext i bools bits (stateLoop inits (body i bools bits)))
      (fun _ bools _ => bools)
      (letObs d dom inits body ext) := by
  refine machine_trace_lets_of_streamBRA d dom inits src (letObs d dom inits body ext) ok hbody
    hinit _ (fun _ bools _ => bools) ?_ hr entry closes hsyn
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

/-- **A machine with one-output combinational children, composed — the run
boundary derived.** From the endpoint carrying `ServedReal` and, per call, the
child's own theorem on any module of a run of its entry in these contexts
(`hfn`; for a gate-compiled child from its `EntryDefines`, for a machine one
from its `MachineDefines`/`MachineCloses`): the composed theorem with no
premise about the calls' modules (`ComposedH` with the trivial `R`). -/
theorem machine_linked_callsR {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module}
    {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (h : MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m dsn)
      declName d m dsn dom src ext (fun _ bools _ => bools) lsrc)
    (hsimple : d.shape.instFields = [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (P : Nat → List Nat → Prop) (F : Nat → List Nat → Nat)
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k args j,
      (d.shape.insts.map (·.2.1))[k]? = some args →
      (∀ q ∈ args, q < d.ls.length ∧ q < (lsrc i bools bits).length) ∧
      P k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) ∧
      F k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) =
        posEnc (fun p => (bools p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
          (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain))
    -- per call: not a memory, and the child's theorem on any run of its entry here
    (hfn : ∀ (k : Nat) (c : Name), (d.shape.insts.map (·.1))[k]? = some c →
      Sparkle.Compiler.MachMemory.memChild? c = none ∧
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (mc : Sparkle.IR.AST.Module) (Dc : Design)
        (w w' : Void IO.RealWorld),
        Tools.ShippingChildInv.InvW mref cref w →
        RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w (mc, Dc) w' →
        ChildFn mc (P k) (F k)) :
    Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) declName d kD m dsn dom src ext := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems hsrc hpass hrst hinit _
  exact Tools.ShippingMachineCompose.machine_linked_of nd len rnd rlen llen wired trace hsimple kD hkD
    hI hIlen hSL hSlen hLlen hNIn P F i bools bits T seed st0 mems hsrc hpass hrst hinit
    (fun k args mc st hargs hst hcs hmod => by
      have hk : k < d.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
      have hc : (d.shape.insts.map (·.1))[k]? = some (d.shape.insts[k]).1 := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hk]; rfl
      obtain ⟨hnone, hf⟩ := hfn k _ hc
      rcases hx.2 hsimple k hk args mc st hargs hst hcs hmod with ⟨md, hmd, _⟩ | ⟨Dc, hrc, _⟩
      · rw [hnone] at hmd; cases hmd
      · obtain ⟨mctx', cctx', w, w', hw, hrun⟩ := hrc.inv
        exact hf mctx' cctx' mc Dc w w' hw hrun)
    (fun k args j hk _ => hcalls i bools bits k args j hk)

/-- `machine_traceL_of_data_extRA` from the all-worlds closing premise. -/
theorem machine_traceL_of_data_extR {declName : Name} (d : MachineData) {ι : Type}
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
    (hr : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (m, design) w')
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : MachineCloses mctx mref cctx cref declName d.shape)
    (hsyn : Tools.ShippingChildInv.ChildBnd mref cref w) :
    MachineTraceLBX (ServedReal mctx mref cctx cref declName d.shape m design) declName d m design dom src
      (fun i bools bits => ext i bools bits (stateLoop inits (body i bools bits)))
      (fun _ bools _ => bools)
      (letObs d dom inits body ext) :=
  machine_traceL_of_data_extRA d dom inits body obsR ext src ok hbody hinit writes hres hsrc hext hr entry (Tools.ShippingChildInv.machineClosesAt_of_closes closes) hsyn

end Tools.ShippingMachineComposeR
