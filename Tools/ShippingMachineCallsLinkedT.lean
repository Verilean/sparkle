import Tools.ShippingMachineMemLinked
import Tools.ShippingMachineSeqInst

/-! # A machine with memory and sequential calls, composed with its children

`machine_linkedT` composes a machine with its children given, per instance,
the child's own run. Here every call is either a memory read (its instance
is the built memory module, `mem_hchild`) or a call of a sequential machine
child (its instance is a module whose run over time is described by
`SeqChildRun`, `seq_inst_run`). The argument values a sequential child sees
are the `let` observations of the call's arguments (`valsOf`); its outputs
on them are the call's values at the call's ports. -/
namespace Tools.ShippingMachineCallsLinkedT
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierState
open Tools.ShippingMachineLinkedT Tools.ShippingMachineMemLinked Tools.ShippingMachineSeqInst
open Sparkle.IR.Machine (moduleByName OutField)
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineCompose (argPorts)

/-- The argument values a call's child sees at time `τ`: the observations of
its argument `let`s. -/
def valsOf (lsrc : List (Nat → Nat)) (args : List Nat) : Nat → List Nat :=
  fun τ => args.map fun l => (lsrc[l]?.map (· τ)).getD 0

/-- A memory read's facts (`mem_hchild`). -/
def MemFacts {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape)
    (lsrc : List (Nat → Nat)) (nL : Nat) (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (kD : Nat) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n)) (k : Nat) (c : Name) : Prop :=
  ∃ (cb : Bool) (aw dw : Nat) (A : Signal D (BitVec aw)) (Dd : Signal D (BitVec dw))
    (E : Signal D Bool) (R : Signal D (BitVec aw)) (l0 l1 l2 l3 : Nat),
    Sparkle.Compiler.MachMemory.memChild? c =
      some (Sparkle.Compiler.MachMemory.memModule cb aw dw) ∧
    (shape.insts.map (·.2.1))[k]? = some [l0, l1, l2, l3] ∧
    lsrc[l0]? = some (fun j => (A.val j).toNat) ∧ l0 < nL ∧
    lsrc[l1]? = some (fun j => (Dd.val j).toNat) ∧ l1 < nL ∧
    lsrc[l2]? = some (fun j => if E.val j then 1 else 0) ∧ l2 < nL ∧
    lsrc[l3]? = some (fun j => (R.val j).toNat) ∧ l3 < nL ∧
    (bsI[k]?.map (·.2)) = some (.bits dw) ∧
    ∀ j, (ext (kD + k) dw).val j = (memRead cb A Dd E R).val j

/-- `mc` is the module of an instance statement serving call `k`. -/
abbrev InstOfCall (body : List Stmt) (mc : Module) (k : Nat) : Prop :=
  ∃ (iname : String) (argWs : List String) (outs : List (Nat × String)) (outWs : List String),
    Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ body ∧ ∃ e ∈ outs, e.1 = k

/-- Arguments that are `let`s have observations. -/
theorem args_facts {lsrc : List (Nat → Nat)} {nL : Nat} {args : List Nat}
    (hall : args.all (· < nL) = true) (hlen : lsrc.length = nL) :
    ∀ (q : Nat) (hq : q < args.length), args[q] < nL ∧ ∃ g, lsrc[args[q]]? = some g := by
  intro q hq
  have hlt : args[q] < nL := by
    have := List.all_eq_true.mp hall _ (List.getElem_mem hq)
    simpa using this
  exact ⟨hlt, _, List.getElem?_eq_getElem (by rw [hlen]; exact hlt)⟩

/-- A sequential call's facts: the instance of the call runs as its child
(`SeqChildRun`, the boundary), its arguments are `let`s, their values in
range, and the call's value at its port is the child's output on them. -/
def SeqFacts {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape) (dsn : Design)
    (body : List Stmt) (lsrc : List (Nat → Nat)) (nL : Nat)
    (bsI : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)) (kD : Nat)
    (extB : Nat → Signal D Bool) (ext : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (bsC : Name → List (Name × Sparkle.Compiler.Elab.MixedGateBinder))
    (outsC : Name → List OutField) (S : Name → (Nat → List Nat) → List (Nat → Nat))
    (k : Nat) (c : Name) : Prop :=
  Sparkle.Compiler.MachMemory.memChild? c = none ∧
  ∃ args : List Nat, (shape.insts.map (·.2.1))[k]? = some args ∧
    (∀ mc : Module, moduleByName dsn.modules mc.name = some mc → InstOfCall body mc k →
      SeqChildRun mc (bsC c) (outsC c) (S c) ∧ (argPorts mc).length = args.length) ∧
    (∀ (q : Nat) (hq : q < args.length), args[q] < nL ∧ ∃ g, lsrc[args[q]]? = some g) ∧
    (∀ τ, Tools.ShippingMachineChild.InRange (valsOf lsrc args τ)
      ((bsC c).filter fun b => b.2 != .domain)) ∧
    ∃ (k' : Nat) (o : OutField) (f : Nat → Nat), (outsC c)[k']? = some o ∧
      o.name = shape.instFields.getD k "" ∧ (S c (valsOf lsrc args))[k']? = some f ∧
      ∀ τ, Tools.ShippingMachineEntry.posEnc (fun p => (extB p).val τ) (fun p n => (ext p n).val τ)
        (kD + k) ((bsI[k]?.map (·.2)).getD .domain) = f τ

/-- **Memory and sequential children satisfy the composition's premise.** -/
theorem calls_hchild {D : DomainConfig} (shape : Sparkle.Compiler.Elab.MachineShape)
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
    (hcalls : ∀ k c, (shape.insts.map (·.1))[k]? = some c →
      MemFacts shape lsrc nL bsI kD ext k c ∨
      SeqFacts shape dsn body lsrc nL bsI kD extB ext bsC outsC S k c) :
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
    obtain ⟨hrun, hlenA⟩ := hbound0 mc hmc ⟨iname, argWs, outs, outWs, hinst, e0, he0, rfl⟩
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
      · obtain ⟨_, args1, hargs1, hbound1, _, hrange1, k', o, f, hk', hon, hf, hpos⟩ := hs
        have hargsEq : args1 = args0 := by
          rw [(hall e hem).1] at hargs1; exact (Option.some.inj hargs1).symm
        subst hargsEq
        obtain ⟨hrun1, _⟩ := hbound1 mc hmc ⟨iname, argWs, outs, outWs, hinst, e, hem, rfl⟩
        refine ⟨bsC c, outsC c, S c, hrun1, fun τ _ => hrange1 τ, k', o, f, hk',
          by rw [hon, (hall e hem).2.1], hf, ?_⟩
        intro t ht
        rw [hPo t ht idx e w he hw]
        exact hpos (T - 1 - t)

open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge in
open Sparkle.IR.Machine Sparkle.Compiler.Elab in
/-- **A machine whose calls are memory reads and sequential machine children,
composed with its children.** From the open endpoint (`MachineTraceLB`): the
STATEFUL linked run of the emitted module — each memory instance stepping
its memory from zero, each sequential instance its child module from reset —
seeded with the declaration's own inputs only (reset and clock held low),
shows the source, given per call its facts (`MemFacts` / `SeqFacts`). -/
theorem machine_linkedT_calls {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
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
    (h : MachineTraceLB declName d m dsn dom src ext extB lsrc)
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
    (hcalls : ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) k c,
      (d.shape.insts.map (·.1))[k]? = some c →
      MemFacts d.shape (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD (ext i bools bits) k c ∨
      SeqFacts d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
        (extB i bools bits) (ext i bools bits) bsC outsC (S i) k c) :
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
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩ :=
    machine_linkedT h hfe kD hkD hI hIlen hSL hSlen hLlen hNIn
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit hm0 hst0 hreg
  exact H i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit
    (calls_hchild d.shape dsn m.body (lsrc i bools bits) d.ls.length (d.bsIn.drop kD) kD
      (extB i bools bits) (ext i bools bits) bsC outsC (S i) _ _ _ T kids hm0 hst0 hreg
      (hcalls i bools bits))

/-! ## A sequential call's argument stream, decoded -/

open Tools.ShippingMachineChild in
theorem decB_valsOf {D : DomainConfig} {bs : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {lsrc : List (Nat → Nat)} {args : List Nat} {p q : Nat} {A : Signal D Bool}
    (hp : portIdx bs p = q) (hq : q < args.length)
    (hl : lsrc[args[q]]? = some (fun τ => Tools.ShippingMuxLoweringSoundness.encodeBool (A.val τ)))
    (τ : Nat) : decB bs (valsOf lsrc args τ) p = A.val τ := by
  simp only [decB, valsOf, hp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hq, Option.map_some, Option.getD_some, hl]
  exact encodeBool_ne _

open Tools.ShippingMachineChild in
theorem decV_valsOf {D : DomainConfig} {bs : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {lsrc : List (Nat → Nat)} {args : List Nat} {p q n : Nat} {B : Signal D (BitVec n)}
    (hp : portIdx bs p = q) (hq : q < args.length)
    (hl : lsrc[args[q]]? = some (fun τ => (B.val τ).toNat)) (τ : Nat) :
    decV bs (valsOf lsrc args τ) p n = B.val τ := by
  simp only [decV, valsOf, hp, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hq, Option.map_some, Option.getD_some, hl, BitVec.ofNat_toNat,
    BitVec.setWidth_eq]

open Tools.ShippingMachineChild in
/-- A decoded Bool input is the Signal whose values it decodes. -/
theorem boolsOf_at {D : DomainConfig} {bs : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {vals : Nat → List Nat} {p : Nat} {A : Signal D Bool}
    (h : ∀ τ, decB bs (vals τ) p = A.val τ) : (boolsOf bs vals p : Signal D Bool) = A := by
  cases A with
  | mk a =>
    show (⟨fun τ => decB bs (vals τ) p⟩ : Signal D Bool) = ⟨a⟩
    congr 1
    funext τ; exact h τ

open Tools.ShippingMachineChild in
/-- A decoded bit-vector input is the Signal whose values it decodes. -/
theorem bitsOf_at {D : DomainConfig} {bs : List (Name × Sparkle.Compiler.Elab.MixedGateBinder)}
    {vals : Nat → List Nat} {p n : Nat} {B : Signal D (BitVec n)}
    (h : ∀ τ, decV bs (vals τ) p n = B.val τ) : (bitsOf bs vals p n : Signal D (BitVec n)) = B := by
  cases B with
  | mk b =>
    show (⟨fun τ => decV bs (vals τ) p n⟩ : Signal D (BitVec n)) = ⟨b⟩
    congr 1
    funext τ; exact h τ

/-- A function of the decoded inputs is that function of any families they equal. -/
theorem decoded_eq {D : DomainConfig} {α : Type}
    (F : (Nat → Signal D Bool) → ((j : Nat) → (n : Nat) → Signal D (BitVec n)) → α)
    {bools bools' : Nat → Signal D Bool}
    {bits bits' : (j : Nat) → (n : Nat) → Signal D (BitVec n)}
    (hb : bools = bools') (hv : bits = bits') : F bools bits = F bools' bits' := by
  rw [hb, hv]

end Tools.ShippingMachineCallsLinkedT
