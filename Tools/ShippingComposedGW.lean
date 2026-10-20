import Tools.ShippingMachineCallsLinkedTG
import Tools.ShippingMachineShipsHier
-- Round par/sat. BUILT: sa1 (ComposedGW, NoPortsTypedBW exit ok; SatInputs failed: 7 tactic/term errors, fixed by the worker), sa2 (all, exit 0, 669 jobs).

/-! # `ComposedGW`: the composed statement exporting its registers' wiring (round par/sat)

`Tools.ShippingMachineShipsHier.ComposedG` exports of its existential `regs` only
`regs.Nodup ∧ regs.length = d.ss.length`. A user of a head built on it
(`machine_design_noPortsTB`) must discharge `∀ t st r, r ∈ regs → seedIn b ins t st r = st r`,
i.e. know that no register is an input port: impossible with `regs` opaque.

The producer has the fact: `machine_linkedT_callsRG` destructures the trace
(`MachineTraceLBX`) into `ids, cache, regs, lets, wired : MachineWired …` and drops `wired`.
Here:

* `Tools.ShippingMachineCallsLinkedTG.machine_linkedT_callsRGW`: the same theorem (same binders,
  in the same order, so a generated application of `machine_linkedT_callsRG` stays well-typed
  with the head constant swapped) whose conclusion ALSO exports
  `∃ lets, MachineWired declName d.shape ids cache m dsn regs lets` — a strengthened
  conclusion; no hypothesis added;
* `Tools.ShippingComposedGW.ComposedGW`: `ComposedG` with that conjunct;
  `ComposedGW.toG` forgets it;
* `composedGW_of_T`: `composedG_of_T` (same binders) for the strengthened statement.

No new fact about the compiler; nothing added to `RefLaws` or a trusted list. -/
namespace Tools.ShippingMachineCallsLinkedTG
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierState
open Tools.ShippingMachineLinkedT Tools.ShippingMachineMemLinked Tools.ShippingMachineSeqInst
open Tools.ShippingMachineCallsLinkedT Tools.ShippingMachineCallsLinkedTR
open Sparkle.IR.Machine (moduleByName OutField)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCompose (argPorts)
open Tools.ShippingFirstGateChild (ChildFnR)

open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge in
open Sparkle.IR.Machine Sparkle.Compiler.Elab in
/-- **`machine_linkedT_callsRG` exporting the wiring** (round par/sat): the statement of
`machine_linkedT_callsRG` with ONE more conjunct in the conclusion, the trace's `MachineWired`
for the same `ids`, `cache`, `regs` (dropped by `machine_linkedT_callsRG`). The proof is
`machine_linkedT_callsRG`'s, copied, keeping `wired`. Original docstring follows.

**A machine whose calls are memory reads, sequential machine children and
gate-route combinational children, composed with its children — the
child-run boundary derived.** As `machine_linkedT_callsR`, with a third kind
of call (`GateFactsR`, callee kind `gk c = true`); a gate callee's boundary
(`GateRun`) is derived from `ServedReal` and its reflection in the parent's
contexts (`hreflG`: `EntryDefines c (vC c)`). -/
theorem machine_linkedT_callsRGW {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX
      (Tools.ShippingMachineTraceX.ServedReal mctx mref cctx cref declName d.shape m dsn)
      declName d m dsn dom src ext extB lsrc)
    (hfe : d.shape.instFields ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (bsC : Name → List (Name × MixedGateBinder)) (outsC : Name → List OutField)
    (S : ι → Name → (Nat → List Nat) → List (Nat → Nat))
    (shC : Name → Sparkle.Compiler.Elab.MachineShape)
    (gk : Name → Bool) (vC : Name → Lean.Expr) (FC : Name → List Nat → Nat)
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
      (d.shape.insts.map (·.1))[k]? = some c →
      MemFacts d.shape (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD (ext i bools bits) k c ∨
      (gk c = false ∧ SeqFactsR d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
        (extB i bools bits) (ext i bools bits) bsC outsC (S i) shC k c) ∨
      (gk c = true ∧ GateFactsR d.shape (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
        (extB i bools bits) (ext i bools bits) bsC vC FC k c))
    -- the sequential children's reflection facts (as `machine_linkedT_callsR`)
    (hrefl : ∀ (k : Nat) (c : Name), (d.shape.insts.map (·.1))[k]? = some c →
      (d.shape.instOrigins.getD k .ord).child? = none → gk c = false →
      Tools.ShippingMachineEntry.MachineDefines mctx mref cctx cref c (shC c) ∧
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
        Tools.ShippingChildInv.ChildRanIn mref cref c mctx' cctx' →
        Tools.ShippingMachineEntry.MachineCloses mctx' mref cctx' cref c (shC c))
    -- the gate children's reflection: the constant the entry hands on (in the
    -- parent's contexts; it does not depend on them)
    (hreflG : ∀ (k : Nat) (c : Name), (d.shape.insts.map (·.1))[k]? = some c →
      (d.shape.instOrigins.getD k .ord).child? = none → gk c = true →
      Tools.ShippingInlineSoundness.EntryDefines mctx mref cctx cref c (vC c)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      -- (round par/sat) the wiring of the SAME ids, cache, registers
      (∃ lets : List String, Tools.ShippingMachineEntry.MachineWired declName d.shape ids cache m dsn
        regs lets) ∧
      ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
        (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
        (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
        (kids : String → KidState),
        (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
          (fun j => (extB i bools bits j).val (T - 1 - t))
          (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
        (∀ t st r, r ∈ regs → seed t st r = st r) →
        (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
        (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → st0 r = f.init) →
        (∀ iname n a, (kids iname).mems n a = 0) → (∀ iname, (kids iname).st "out_rdata" = 0) →
        (∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
          moduleByName dsn.modules mc.name = some mc →
          ∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body →
            (kids iname).st r = init.toNat) →
        ∃ envs, runModuleT (Tools.ShippingEntrySoundness.weOf m) (childMap dsn.modules) m.body
            seed T st0 mems kids = some envs ∧
          envs.length = T ∧
          ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := h
  -- (writing-time guess, accepted by build sa1/sa2: `wired` is used twice — exported here and passed on below; it is a proof)
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ⟨lets, wired⟩, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit hm0 hst0 hreg
  exact machine_linkedT_of nd len rnd rlen llen wired trace hfe kD hkD hI hIlen hSL hSlen hLlen hNIn
    i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit
    (calls_hchildRG d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
      (extB i bools bits) (ext i bools bits) bsC outsC (S i) _ _ _ T kids hm0 hst0 hreg shC
      gk vC FC
      (fun k c mc iname argWs outs outWs hc hnone hgk hst hout hke hmod => by
        have hk : k < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
        have hck : (d.shape.insts[k]).1 = c := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc; simpa using hc
        rcases hx.1 hfe k hk mc iname argWs outs outWs hst hout hke hmod with ⟨md, hmd, _⟩ | ⟨Dc, hrc, hcons⟩
        · rw [hnone] at hmd; cases hmd
        · rw [hck] at hrc
          obtain ⟨mctx', cctx', w, w', hw, hrun⟩ := hrc.inv
          obtain ⟨hdef, hcl⟩ := hrefl k c hc hnone hgk
          exact ⟨mctx', mref, cctx', cref, w, w', Dc, hrun,
            Tools.ShippingReflectCtx.MachineDefines.ctx hdef,
            hcl mctx' cctx' (Tools.ShippingChildInv.ChildRanIn.of_run hw hrun)⟩)
      (fun k c mc iname argWs outs outWs hc hnone hgk hst hout hke hmod => by
        have hk : k < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
        have hck : (d.shape.insts[k]).1 = c := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc; simpa using hc
        rcases hx.1 hfe k hk mc iname argWs outs outWs hst hout hke hmod with ⟨md, hmd, _⟩ | ⟨Dc, hrc, hcons⟩
        · rw [hnone] at hmd; cases hmd
        · rw [hck] at hrc
          obtain ⟨mctx', cctx', w, w', _, hrun⟩ := hrc.inv
          exact ⟨mctx', mref, cctx', cref, w, w', Dc, hrun,
            Tools.ShippingReflectCtx.EntryDefines.ctx (hreflG k c hc hnone hgk)⟩)
      (hcalls i bools bits))

end Tools.ShippingMachineCallsLinkedTG

namespace Tools.ShippingComposedGW
-- the opens of `Tools/ShippingMachineShipsHier.lean`
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingHierOptRun
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineShipsHier

/-- `ComposedG` whose existential ALSO exports the wiring of the same `ids`, `cache`, `regs`
(`MachineWired` of the core module `m` in its design `dsn`). -/
def ComposedGW {σ : Type} (KS : Design → KStep σ)
    (Reset : Sparkle.IR.AST.Module → Design → (String → σ) → Prop)
    (declName : Name) (d : MachineData) (kD : Nat)
    (m : Sparkle.IR.AST.Module) (dsn : Design) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧
    (∃ lets : List String, MachineWired declName d.shape ids cache m dsn regs lets) ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
      (kids : String → σ),
      (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t))
        (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      Reset m dsn kids →
      ∃ envs, runModuleTG (KS dsn) (Tools.ShippingEntrySoundness.weOf m)
          (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j

/-- Forgetting the wiring. -/
theorem ComposedGW.toG {σ : Type} {KS : Design → KStep σ}
    {Reset : Sparkle.IR.AST.Module → Design → (String → σ) → Prop}
    {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (h : ComposedGW KS Reset declName d kD m dsn dom src ext extB) :
    ComposedG KS Reset declName d kD m dsn dom src ext extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, -, H⟩ := h
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩

/-- **`composedG_of_T` for the strengthened statement**: same implicit binders, in the same
order, as `Tools.ShippingMachineShipsHier.composedG_of_T` (a generated application of the one
stays well-typed with the head swapped, when its `h` is the strengthened conclusion of
`machine_linkedT_callsRGW`). Proof copied, the wiring passed through. -/
theorem composedGW_of_T {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (h : ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
      ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
        regs.Nodup ∧ regs.length = d.ss.length ∧
        (∃ lets : List String, MachineWired declName d.shape ids cache m dsn regs lets) ∧
        ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
          (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
          (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
          (kids : String → KidState),
          (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
            (fun j => (extB i bools bits j).val (T - 1 - t))
            (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
          (∀ t st r, r ∈ regs → seed t st r = st r) →
          (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
          (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
            d.shape.layout.slots[k]? = some f → st0 r = f.init) →
          (∀ iname n a, (kids iname).mems n a = 0) → (∀ iname, (kids iname).st "out_rdata" = 0) →
          (∀ (iname : String) (mc : Sparkle.IR.AST.Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
            moduleByName dsn.modules mc.name = some mc →
            ∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body →
              (kids iname).st r = init.toNat) →
          ∃ envs, runModuleT (Tools.ShippingEntrySoundness.weOf m) (childMap dsn.modules) m.body
              seed T st0 mems kids = some envs ∧
            envs.length = T ∧
            ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
              d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
              (envs[j]'hj) o.name = f j)
    (hm : Tools.ConeFold.memFree m.body) :
    ComposedGW (fun _ => flatKS) Reset1 declName d kD m dsn dom src ext extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, hw, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, hw, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk hinit ⟨h1, h2, h3⟩
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T seed st0 mems kids hin hpass hrst hclk hinit
    h1 h2 h3
  refine ⟨envs, ?_, hlen, hobs⟩
  rw [← runModuleT_flat _ _ _ hm]
  exact hrun

end Tools.ShippingComposedGW
