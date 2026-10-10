import Tools.ShippingMachineCallsLinkedT
import Tools.ShippingMachineTraceX
import Tools.ShippingGateChild

/-! # Sequential children composed, the run boundary derived

`machine_linkedT_calls` takes, per sequential call, the premise that EVERY
instance module of the parent satisfying `InstOfCall` is a run of the call's
child — `InstOfCall` does not bind the call index, so for a parent with two
different children (or a child next to a memory) that premise is false. Here
the instance is the one whose output wires are the call's ports, and that it
is a run of the call's child is DERIVED (`ServedReal`, under `ChildBnd`);
what remains per child is its own theorem and its reflection facts. -/
namespace Tools.ShippingMachineCallsLinkedTR
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierState
open Tools.ShippingMachineLinkedT Tools.ShippingMachineMemLinked Tools.ShippingMachineSeqInst
open Tools.ShippingMachineCallsLinkedT
open Sparkle.IR.Machine (moduleByName OutField)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCompose (argPorts)

/-- A sequential call's facts with the boundary at the CHILD: the child's
own theorem for every module that is a run of the child's entry
(`MachineRun`), instead of a premise about the parent's instances. -/
def SeqFactsR {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape) (dsn : Design)
    (body : List Stmt) (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (kD : Nat)
    (extB : Nat → Signal D Bool) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (bsC : Name → List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (outsC : Name → List OutField) (S : Name → (Nat → List Nat) → List (Nat → Nat))
    (shC : Name → Sparkle.Compiler.Elab.MachineShape) (k : Nat) (c : Name) : Prop :=
  Sparkle.Compiler.MachMemory.memChild? c = none ∧
  ∃ args : List Nat, (shape.insts.map (·.2.1))[k]? = some args ∧
    (∀ mc : Module, Tools.ShippingGateChild.MachineRun c (shC c) mc →
      SeqChildRun mc (bsC c) (outsC c) (S c) ∧ (argPorts mc).length = args.length) ∧
    (∀ (q : Nat) (hq : q < args.length), args[q] < nL ∧ ∃ g, lsrc[args[q]]? = some g) ∧
    (∀ τ, Tools.ShippingMachineChild.InRange (valsOf lsrc args τ)
      ((bsC c).filter fun b => b.2 != .domain)) ∧
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat), (outsC c)[k']? = some o ∧
      o.name = shape.instFields.getD k "" ∧ (S c (valsOf lsrc args))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => (extB p).val τ) (fun p n => (ext p n).val τ)
        (kD + k) ((bsI[k]?.map (·.2)).getD .domain) = f τ

/-- **Memory and sequential children satisfy the composition's premise**, the
instance of a sequential call being a run of the call's child entry
(`hsv`: stated for the instance whose output wires are the call's ports). -/
theorem calls_hchildR {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape)
    (dsn : Design) (body : List Stmt) (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (kD : Nat)
    (extB : Nat → Signal D Bool) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (bsC : Name → List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (outsC : Name → List OutField) (S : Name → (Nat → List Nat) → List (Nat → Nat))
    (names : List String) (offA offO : Nat) (T : Nat) (kids : String → KidState)
    (hm0 : ∀ iname n a, (kids iname).mems n a = 0)
    (hst0 : ∀ iname, (kids iname).st "out_rdata" = 0)
    (hreg : ∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ body) →
      moduleByName dsn.modules mc.name = some mc →
      ∀ r c rs inp init, Stmt.register r c rs inp init ∈ mc.body → (kids iname).st r = init.toNat)
    (shC : Name → Sparkle.Compiler.Elab.MachineShape)
    (hsv : ∀ k c (mc : Module) (iname : String) (argWs : List String) (outs : List (Nat × String))
      (outWs : List String), (shape.insts.map (·.1))[k]? = some c →
      Sparkle.Compiler.MachMemory.memChild? c = none →
      Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ body →
      outs.mapM (fun (k, _) => names[offO + k]?) = some outWs → (∃ e ∈ outs, e.1 = k) →
      moduleByName dsn.modules mc.name = some mc → Tools.ShippingGateChild.MachineRun c (shC c) mc)
    (hcalls : ∀ k c, (shape.insts.map (·.1))[k]? = some c →
      MemFacts shape lsrc nL bsI kD ext k c ∨
      SeqFactsR shape dsn body lsrc nL bsI kD extB ext bsC outsC S shC k c) :
    ∀ (args : List Nat) (outs : List (Nat × String)) (mc : Module) (iname : String)
      (argWs outWs : List String),
      args.mapM (fun j => names[offA + j]?) = some argWs →
      outs.mapM (fun (k, _) => names[offO + k]?) = some outWs →
      moduleByName dsn.modules mc.name = some mc →
      Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ body →
      outs ≠ [] → (outs.map (·.2)).Nodup →
      (outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true →
      (∀ e ∈ outs, (shape.insts.map (·.2.1))[e.1]? = some args ∧
        shape.instFields.getD e.1 "" = e.2 ∧
        ∀ c md, (shape.insts.map (·.1))[e.1]? = some c →
          Sparkle.Compiler.MachMemory.memChild? c = some md → mc = md.1) →
      ∀ Pw : Nat → Env,
        (∀ t, Pw t "rst" = 0) → (∀ t, Pw t "clk" = 0) →
        (∀ t, t < T → ∀ (q : Nat) (hq : q < args.length) (w : String) (g : Nat → Nat),
          argWs[q]? = some w → lsrc[args[q]]? = some g → args[q] < nL →
          Pw t w = g (T - 1 - t)) →
        (∀ t, t < T → ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e →
          outWs[idx]? = some w →
          Pw t w = Tools.ShippingMachineEntry.posEnc (fun p => (extB p).val (T - 1 - t))
            (fun p n => (ext p n).val (T - 1 - t)) (kD + e.1)
            ((bsI[e.1]?.map (·.2)).getD .domain)) →
        ∃ cenvs, runModule (Sparkle.IR.RegDedup.declWidth mc) mc.body
            (fun t cst => connEnvS (inConns mc.outputs (connsG mc argWs outs outWs)) (Pw t) cst)
            T (kids iname).st (kids iname).mems = some cenvs ∧
          ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
            (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
            (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w) := by
  intro args outs mc iname argWs outWs hargsW hout hmc hinst hne hfnd hfields hall Pw hrstP hclkP
    hPa hPo
  obtain ⟨e0, he0⟩ : ∃ e, e ∈ outs := by
    cases outs with
    | nil => exact absurd rfl hne
    | cons e _ => exact ⟨e, List.mem_cons_self⟩
  -- the call of an entry
  have callOf : ∀ e ∈ outs, ∃ c, (shape.insts.map (·.1))[e.1]? = some c := by
    intro e he
    have hk : e.1 < (shape.insts.map (·.2.1)).length :=
      (List.getElem?_eq_some_iff.mp (hall e he).1).1
    exact ⟨_, List.getElem?_eq_getElem (by simpa using hk)⟩
  -- a memory entry's instance has one entry
  have memOne : ∀ e ∈ outs, ∀ c, (shape.insts.map (·.1))[e.1]? = some c →
      MemFacts shape lsrc nL bsI kD ext e.1 c → ∀ e' ∈ outs, e' = e := by
    intro e he c hc hm e' he'
    obtain ⟨cb, aw, dw, _, _, _, _, _, _, _, _, hmc', _⟩ := hm
    have hmm := (hall e he).2.2 c _ hc hmc'
    subst hmm
    have hfo : outs.map (·.2) = ["out"] := by
      apply fields_out (by simpa using hne) hfnd
      intro f hf
      have := List.all_eq_true.mp hfields f hf
      simp only [Sparkle.Compiler.MachMemory.memModule, List.any_cons, List.any_nil, Bool.or_false,
        beq_iff_eq] at this
      exact this.symm
    have hlen : outs.length = 1 := by simpa using congrArg List.length hfo
    match outs, hlen, he, he' with
    | [x], _, he, he' => simp at he he'; rw [he, he']
  obtain ⟨c0, hc0⟩ := callOf e0 he0
  rcases hcalls e0.1 c0 hc0 with hmem | hseq
  · -- a memory read
    apply mem_hchild shape dsn body lsrc nL bsI kD extB ext names offA offO T kids hm0 hst0 args outs
      mc iname argWs outWs hargsW hout hmc hinst hne hfnd hfields hall _ Pw hrstP hclkP hPa hPo
    intro e he c hc
    have := memOne e0 he0 c0 hc0 hmem e he
    subst this
    rw [hc0] at hc; cases hc
    exact hmem
  · -- a sequential call
    obtain ⟨hnone0, args0, hargs0, hbound0, hlsrc0, hrange0, _⟩ := hseq
    have hargsEq : args0 = args := by
      rw [(hall e0 he0).1] at hargs0; exact (Option.some.inj hargs0).symm
    subst hargsEq
    obtain ⟨hrun, hlenA⟩ := hbound0 mc (hsv e0.1 c0 mc iname argWs outs outWs hc0 hnone0 hinst hout ⟨e0, he0, rfl⟩ hmc)
    obtain ⟨hlW, hgetW⟩ := Tools.ShippingMachineInst.mapM_some _ args0 argWs hargsW
    refine seq_inst_run hrun argWs outs outWs Pw T (kids iname) (valsOf lsrc args0)
      (by rw [hlW, hlenA]) ?_ (fun τ _ => hrange0 τ) ?_ hrstP hclkP
      (hreg iname mc ⟨_, hinst⟩ hmc) ?_
    · intro f hf
      have := List.all_eq_true.mp hfields f hf
      obtain ⟨p, hp, hpf⟩ := List.any_eq_true.mp this
      exact List.mem_map.mpr ⟨p, hp, by simpa using hpf⟩
    · intro t ht
      apply List.ext_getElem (by simp [hlW, valsOf])
      intro q h1 h2
      have hq : q < args0.length := by rw [← hlW]; simpa using h1
      obtain ⟨hlt, g, hg⟩ := hlsrc0 q hq
      obtain ⟨w, hw, hwq⟩ := hgetW q hq
      simp only [List.getElem_map, valsOf]
      have hwq' : argWs[q] = w := by
        have := List.getElem?_eq_getElem (l := argWs) (by simpa using h1)
        rw [hwq] at this; exact (Option.some.inj this).symm
      rw [hwq', hPa t ht q hq w g hwq hg hlt, hg]
      rfl
    · intro idx e w he hw
      have hem : e ∈ outs := List.mem_of_getElem? he
      obtain ⟨c, hc⟩ := callOf e hem
      rcases hcalls e.1 c hc with hm | hs
      · -- a memory entry would be the only one, the sequential call itself
        have := memOne e hem c hc hm e0 he0
        subst this
        rw [hc0] at hc; cases hc
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hmc', _⟩ := hm
        rw [hnone0] at hmc'; cases hmc'
      · obtain ⟨hnone1, args1, hargs1, hbound1, _, hrange1, k', o, f, hk', hon, hf, hpos⟩ := hs
        have hargsEq : args1 = args0 := by
          rw [(hall e hem).1] at hargs1; exact (Option.some.inj hargs1).symm
        subst hargsEq
        obtain ⟨hrun1, _⟩ := hbound1 mc (hsv e.1 c mc iname argWs outs outWs hc hnone1 hinst hout ⟨e, hem, rfl⟩ hmc)
        refine ⟨bsC c, outsC c, S c, hrun1, fun τ _ => hrange1 τ, k', o, f, hk',
          by rw [hon, (hall e hem).2.1], hf, ?_⟩
        intro t ht
        rw [hPo t ht idx e w he hw]
        exact hpos (T - 1 - t)

open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge in
open Sparkle.IR.Machine Sparkle.Compiler.Elab in
/-- **A machine whose calls are memory reads and sequential machine children,
composed with its children — the child-run boundary derived.** As
`machine_linkedT_calls`, from the endpoint carrying `ServedReal` (the run's
instances serving the calls are runs of the calls' children, from
`ChildBnd`): the per-call premise is the CHILD's own theorem for runs of its
entry (`SeqFactsR`) and the children's reflection facts — no premise about the
parent's instances (`BoundaryOf`). -/
theorem machine_linkedT_callsR {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
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
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
      (d.shape.insts.map (·.1))[k]? = some c →
      MemFacts d.shape (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD (ext i bools bits) k c ∨
      SeqFactsR d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
        (extB i bools bits) (ext i bools bits) bsC outsC (S i) shC k c)
    -- the children's reflection facts, in whatever Meta and Core contexts a
    -- child was synthesised (over the parent's state references)
    (hrefl : ∀ (k : Nat) (c : Name), (d.shape.insts.map (·.1))[k]? = some c →
      Sparkle.Compiler.MachMemory.memChild? c = none →
      ∀ (mctx' : Meta.Context) (cctx' : Core.Context),
      Tools.ShippingMachineEntry.MachineDefines mctx' mref cctx' cref c (shC c) ∧
        Tools.ShippingMachineEntry.MachineCloses mctx' mref cctx' cref c (shC c)) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
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
        -- the children start from reset: memories and read latches zero, registers at
        -- their reset values
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
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit hm0 hst0 hreg
  exact machine_linkedT_of nd len rnd rlen llen wired trace hfe kD hkD hI hIlen hSL hSlen hLlen hNIn
    i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit
    (calls_hchildR d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
      (extB i bools bits) (ext i bools bits) bsC outsC (S i) _ _ _ T kids hm0 hst0 hreg shC
      (fun k c mc iname argWs outs outWs hc hnone hst hout hke hmod => by
        have hk : k < d.shape.insts.length := by
          have := (List.getElem?_eq_some_iff.mp hc).1; simpa using this
        have hck : (d.shape.insts[k]).1 = c := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hk] at hc; simpa using hc
        rcases hx.1 hfe k hk mc iname argWs outs outWs hst hout hke hmod with ⟨md, hmd, _⟩ | ⟨Dc, hrc, hcons⟩
        · rw [hck, hnone] at hmd; cases hmd
        · rw [hck] at hrc
          obtain ⟨mctx', cctx', w, w', _, hrun⟩ := hrc.inv
          obtain ⟨hdef, hcl⟩ := hrefl k c hc hnone mctx' cctx'
          exact ⟨mctx', mref, cctx', cref, w, w', Dc, hrun, hdef, hcl⟩)
      (hcalls i bools bits))

end Tools.ShippingMachineCallsLinkedTR
