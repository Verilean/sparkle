import Tools.ShippingMachineLinkedT
import Tools.ShippingHierStateG
-- ORIGIN DISPATCH (par/o-close, compiler change "explicit call-entry origin"):
-- BUILT against the origin-tag compiler (integration run ig4, 3 GiB, swap 0, -j 1, exit 0; fixes: see docs/parallel/O-origin-integration.md).

/-! # `machine_linkedT` at every depth

`machine_linkedT` composes a machine with children stepped flat. Here the
children are stepped by any `KS` reading the parent only through their input
connections (`ShippingHierStateG`): with `flatKS` it is one level; with
`succKS` the children are themselves machines with stateful children. -/
namespace Tools.ShippingMachineLinkedTG
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked
open Tools.ShippingHierState Tools.ShippingMachineCompose Tools.ShippingHierStateG
open Tools.ShippingMachineLinkedT
open Tools.ShippingEntrySoundness (weOf)

/-- **`machine_linkedT` for any child step** — a machine with structure / sequential / memory calls, composed with its
children.** From the open endpoint (`MachineTraceLB`), the STATEFUL linked
run of the emitted module, seeded with the declaration's own inputs only,
shows the source, provided every instance's child — run on environments
whose argument wires carry the source's argument values (the `let`
observations) and whose output wires carry the source's call values — shows
those output values. -/
theorem machine_linkedTG_of {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
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
    {ids : List FVarId} (nd : ids.Nodup) (len : ids.length = d.shape.binders.length)
    {cache : IO.Ref (ExprStructMap String)} {regs : List String} (rnd : regs.Nodup)
    (rlen : regs.length = d.ss.length) {lets : List String} (llen : lets.length = d.letBs.length)
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (trace :
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName d.bsIn ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t))
        (fun j n => (ext i bools bits j n).val (T - 1 - t))
        (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ∃ envs, runModule (weOf m) m.body seed T st0 mems = some envs ∧ envs.length = T ∧
        (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j) ∧
        ∀ j (hj : j < envs.length) (q : Nat) (name : String) (g : Nat → Nat),
          lets[q]? = some name → (lsrc i bools bits)[q]? = some g → q < d.ls.length →
          (envs[j]'hj) name = g j)
    (hfe : d.shape.instFields ≠ [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length) :
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
      -- every instance's child, on the source's argument and call values
      (∀ (args : List Nat) (outs : List (Nat × String)) (mc : Module) (iname : String)
          (argWs outWs : List String),
        args.mapM (fun j => ((machPorts declName ids cache d.shape.binders).map (·.name))[
          machNIn d.shape + d.shape.insts.length + d.shape.layout.slots.length + j]?) =
          some argWs →
        outs.mapM (fun (k, _) => ((machPorts declName ids cache d.shape.binders).map (·.name))[
          machNIn d.shape + k]?) = some outWs →
        moduleByName dsn.modules mc.name = some mc →
        Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ m.body →
        outs ≠ [] → (outs.map (·.2)).Nodup →
        (outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true →
        (∀ e ∈ outs, (d.shape.insts.map (·.2.1))[e.1]? = some args ∧
          d.shape.instFields.getD e.1 "" = e.2 ∧
          ∀ c md, (d.shape.insts.map (·.1))[e.1]? = some c →
            (d.shape.instOrigins.getD e.1 .ord).child? = some md → mc = md.1) →
        ∀ Pw : Nat → Env,
          (∀ t, Pw t "rst" = 0) → (∀ t, Pw t "clk" = 0) →
          (∀ t, t < T → ∀ (q : Nat) (hq : q < args.length) (w : String) (g : Nat → Nat),
            argWs[q]? = some w → (lsrc i bools bits)[args[q]]? = some g → args[q] < d.ls.length →
            Pw t w = g (T - 1 - t)) →
          (∀ t, t < T → ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e →
            outWs[idx]? = some w →
            Pw t w = posEnc (fun p => (extB i bools bits p).val (T - 1 - t))
              (fun p n => (ext i bools bits p n).val (T - 1 - t)) (kD + e.1)
              (((d.bsIn.drop kD)[e.1]?.map (·.2)).getD .domain)) →
          ∃ cenvs, runKS KS mc (Sparkle.IR.RegDedup.declWidth mc)
              (inConns mc.outputs (connsG mc argWs outs outWs)) Pw T (kids iname) = some cenvs ∧
            ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
              (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
              (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w)) →
      ∃ envs, runModuleTG KS (weOf m) (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ =
          some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j := by
  intro i bools bits T seed st0 mems kids hin hpass hrst hclk0 hinit hchild
  have hconds := Tools.ShippingMachineComposedT.wired_runT_conds wired hfe
  obtain ⟨hwf, hnd, hnofb⟩ := hconds
  obtain ⟨nnd, alloc, regsIn, hlets, _, _, link, _, _, _, _, gInsts, gCalls, hnames, hnoCR, _⟩ := wired
  have gInsts := gInsts hfe
  have gCalls := gCalls hfe
  -- the ports: the declaration's, the calls', then the slots' and `let`s'
  let bsD := d.bsIn.take kD
  let bsI := d.bsIn.drop kD
  let names := (machPorts declName ids cache d.shape.binders).map (·.name)
  have hbin : d.shape.binders = (bsD ++ bsI) ++ (d.slotBs ++ d.letBs) := by
    rw [List.take_append_drop, ← List.append_assoc]; exact d.binders_split
  have hlenB : (bsD ++ bsI).length + (d.slotBs ++ d.letBs).length ≤ ids.length := by
    rw [len, hbin]; simp only [List.length_append]; omega
  obtain ⟨restP, hrestP⟩ := machPorts_append (declName := declName) (cache := cache)
    (bsD ++ bsI) (d.slotBs ++ d.letBs) hlenB
  have hlenDI : bsD.length + bsI.length ≤ ids.length := by
    have := hlenB; simp only [List.length_append] at this ⊢; omega
  obtain ⟨insP, hinsP⟩ := machPorts_append (declName := declName) (cache := cache) bsD bsI hlenDI
  have hDlen : (machPorts declName ids cache bsD).length = machNIn d.shape := by
    rw [hNIn]; exact machPorts_length bsD (by omega)
  have hDIlen : (machPorts declName ids cache (bsD ++ bsI)).length =
      machNIn d.shape + d.shape.insts.length := by
    rw [machPorts_length _ (by omega), List.filter_append, List.length_append, ← hNIn,
      List.filter_eq_self.mpr (fun b hb => by simpa using hI b hb), hIlen]
  have hinsLen : insP.length = d.shape.insts.length := by
    have := congrArg List.length hinsP
    rw [List.length_append, hDIlen, hDlen] at this; omega
  have hnamesEq : names = ((machPorts declName ids cache bsD).map (·.name) ++
      insP.map (·.name)) ++ restP.map (·.name) := by
    simp only [names]
    rw [show machPorts declName ids cache d.shape.binders =
      machPorts declName ids cache ((bsD ++ bsI) ++ (d.slotBs ++ d.letBs)) by rw [← hbin],
      hrestP, hinsP, List.map_append, List.map_append]
  have hallLen : names.length =
      machNIn d.shape + d.shape.insts.length + d.shape.layout.slots.length +
        d.shape.layout.lets := by
    have hrestLen : restP.length = d.shape.layout.slots.length + d.shape.layout.lets := by
      have h1 := congrArg List.length hrestP
      rw [List.length_append, machPorts_length _ (by simp only [List.length_append] at hlenB ⊢; omega),
        machPorts_length _ (by omega : (bsD ++ bsI).length ≤ ids.length), List.filter_append,
        List.length_append,
        (List.filter_eq_self (l := d.slotBs ++ d.letBs)).mpr (fun b hb => by simpa using hSL b hb),
        List.length_append, hSlen, hLlen] at h1
      omega
    rw [hnamesEq]
    simp only [List.length_append, List.length_map, hDlen, hinsLen, hrestLen]
    omega
  -- the calls' port names
  let insNames := insP.map (·.name)
  have hinsAt : ∀ k, k < d.shape.insts.length →
      names[machNIn d.shape + k]? = insNames[k]? := by
    intro k hk
    rw [hnamesEq, List.append_assoc, List.getElem?_append_right (by simp [hDlen]),
      List.getElem?_append_left (by simp [hinsLen, hDlen]; omega)]
    simp [hDlen, insNames]
  have hnd' : ((machPorts declName ids cache (bsD ++ bsI)).map (·.name)).Nodup := by
    have := nnd
    rw [show (machPorts declName ids cache d.shape.binders).map (·.name) = names from rfl,
      hnamesEq, ← List.map_append, ← hinsP] at this
    exact (List.nodup_append.mp this).1
  have hinsNd : insNames.Nodup := by
    rw [hinsP, List.map_append] at hnd'
    exact (List.nodup_append.mp hnd').2.1
  -- the values of the calls, by cycle
  let V : Nat → Nat → Nat := fun k j =>
    posEnc (fun p => (extB i bools bits p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
      (((bsI)[k]?.map (·.2)).getD .domain)
  let seed' : Nat → (String → Nat) → Env := fun t st x =>
    if x ∈ insNames then V (insNames.idxOf x) (T - 1 - t) else seed t st x
  have hoff : ∀ t st x, x ∉ insNames → seed' t st x = seed t st x := by
    intro t st x hx; simp [seed', hx]
  have hon : ∀ t st k p, insP[k]? = some p →
      seed' t st p.name = V k (T - 1 - t) := by
    intro t st k p hp
    have hmem : p.name ∈ insNames := List.mem_map_of_mem (List.mem_of_getElem? hp)
    have hidx : insNames.idxOf p.name = k := by
      have hk : k < insP.length := (List.getElem?_eq_some_iff.mp hp).1
      have : insNames[k]'(by simp [insNames]; exact hk) = p.name := by
        simp [insNames, (List.getElem?_eq_some_iff.mp hp).2]
      rw [← this]; exact idxOf_nodup hinsNd k _
    simp [seed', hmem, hidx]
  -- registers and reset are not calls' ports
  have notIns : ∀ x ∈ names.drop (names.length - d.shape.layout.lets -
      d.shape.layout.slots.length), x ∉ insNames := by
    intro x hx hxi
    have hdrop : names.drop (names.length - d.shape.layout.lets - d.shape.layout.slots.length) =
        restP.map (·.name) := by
      have hL : names.length - d.shape.layout.lets - d.shape.layout.slots.length =
          ((machPorts declName ids cache bsD).map (·.name) ++ insP.map (·.name)).length := by
        rw [hallLen]; simp [hDlen, hinsLen]
      rw [hL, hnamesEq, List.drop_left]
    rw [hdrop] at hx
    have := nnd
    rw [show (machPorts declName ids cache d.shape.binders).map (·.name) = names from rfl,
      hnamesEq] at this
    have hd := (List.nodup_append.mp this).2.2
    exact hd x (List.mem_append_right _ hxi) x hx rfl
  have rstNot : "rst" ∉ insNames := by
    intro h
    have : "rst" ∈ names := by
      rw [hnamesEq]; exact List.mem_append_left _ (List.mem_append_right _ h)
    exact Tools.ShippingRegisterSoundness.not_allocated_rst (alloc _ this)
  have clkNot : "clk" ∉ insNames := by
    intro h
    have : "clk" ∈ names := by
      rw [hnamesEq]; exact List.mem_append_left _ (List.mem_append_right _ h)
    exact Tools.ShippingMachineCleanup.not_allocated_clk (alloc _ this)
  -- the open run from `seed'`
  have hlenIds : ids.length = d.shape.binders.length := len
  obtain ⟨envs, hrun, hlenE, hobs, hletobs⟩ := trace i bools bits T seed' st0 mems
    (by
      intro t st ht
      have hsrc := sourceInputs_extend (declName := declName) nd hlenDI hI hnd' (hin t st ht)
        (env' := seed' t st) (fun x hx => hoff t st x (by rwa [hinsP, List.drop_left' (by
          simp)] at hx))
        (fun k p b hp hb => by
          rw [hinsP, List.drop_left' (by simp)] at hp
          rw [hon t st k p hp]
          simp only [V, hb, Option.map_some, Option.getD_some]
          congr 1; simp [bsD]; omega)
      rw [show d.bsIn = bsD ++ bsI from (List.take_append_drop _ _).symm]
      exact hsrc)
    (by
      intro t st r hr
      rw [hoff t st r (notIns r (regsIn r hr))]
      exact hpass t st r hr)
    (by intro t st; rw [hoff t st _ rstNot]; exact hrst t st)
    hinit
  -- a call's port is the output wire of its group's instance
  have portOut : ∀ k, k < d.shape.insts.length →
      insNames[k]? ∈ (bodyInstOuts (childMap dsn.modules) m.body).map some := by
    intro k hk
    obtain ⟨st, hst, args, outs, mc, hcall, hmc, hkmem, _⟩ := gCalls k hk
    obtain ⟨outWs, argWs, iname, hout, _, _, _, hfields, hfnd, hdisj, hnclk, hnrst, _, _, rfl⟩ :=
      hcall
    obtain ⟨idx, hidx, hidxe⟩ := List.getElem_of_mem hkmem
    obtain ⟨hlo, hgeto⟩ := Tools.ShippingMachineInst.mapM_some _ outs outWs hout
    obtain ⟨w, hw, hwi⟩ := hgeto idx hidx
    rw [hidxe] at hw
    have hwk : insNames[k]? = some w := by rw [← hinsAt k hk]; exact hw
    rw [hwk]
    apply List.mem_map_of_mem
    apply bodyInstOuts_of_mem hst
    have hf : (d.shape.instFields.getD k "") ∈ outs.map (·.2) :=
      List.mem_map.mpr ⟨_, hkmem, rfl⟩
    have hpair : (d.shape.instFields.getD k "", w) ∈ (outs.map (·.2)).zip outWs := by
      have hidx' : idx < ((outs.map (·.2)).zip outWs).length := by simp [hlo]; omega
      have : ((outs.map (·.2)).zip outWs)[idx]? = some (d.shape.instFields.getD k "", w) := by
        rw [List.getElem?_zip_eq_some]
        refine ⟨?_, hwi⟩
        rw [List.getElem?_map, List.getElem?_eq_getElem hidx, hidxe]; rfl
      exact List.mem_of_getElem? this
    have hout' := connsG_out (mc := mc) (argWs := argWs)
      (List.all_eq_true.mp hfields _ hf) hfnd
      (by
        cases hc : (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").any
          (·.name == d.shape.instFields.getD k "")
        · rfl
        · exfalso
          have : (outs.map (·.2)).any (fun f =>
              (mc.inputs.filter fun p => p.name != "clk" && p.name != "rst").any (·.name == f)) =
              true := List.any_eq_true.mpr ⟨_, hf, hc⟩
          rw [hdisj] at this; cases this)
      (fun he => hnclk (by rw [← he]; exact List.contains_iff_mem.mpr hf))
      (fun he => hnrst (by rw [← he]; exact List.contains_iff_mem.mpr hf)) hpair
    simp only [stmtInstOuts, childMap, hmc, Option.map_some]
    exact hout'
  have hoff' : ∀ t st n, n ∉ bodyInstOuts (childMap dsn.modules) m.body →
      seed' t st n = seed t st n := by
    intro t st n hn
    apply hoff
    intro hni
    obtain ⟨k, hk, hkn⟩ := List.getElem_of_mem hni
    have hk' : k < d.shape.insts.length := by simp [insNames, hinsLen] at hk; exact hk
    have := portOut k hk'
    rw [List.getElem?_eq_getElem hk, hkn] at this
    obtain ⟨n', hn', hnn⟩ := List.mem_map.mp this
    cases hnn
    exact hn hn'
  obtain ⟨_, henvs⟩ := runModule_envs (weOf m) m.body seed' T st0 mems envs hrun
  refine ⟨envs, ?_, hlenE, hobs⟩
  have hseed : ∀ t st mems' envF, evalAssigns (weOf m) mems' m.body (seed' t st) = some envF →
      seed' t st = seedOuts (childMap dsn.modules) m.body envF (seed t st) := by
    intro t st mems' envF hF
    funext x
    unfold seedOuts
    split
    · rename_i hc
      have hx : x ∈ bodyInstOuts (childMap dsn.modules) m.body := by simpa using hc
      exact (evalAssigns_frame (weOf m) mems' (childMap dsn.modules) m.body _ envF x hwf hF
        (instOuts_not_written m.body x hwf hx)).symm
    · rename_i hc
      exact hoff' t st x (by simpa using hc)
  refine runModuleTG_of_childRuns KS hloc (weOf m) (childMap dsn.modules) m.body seed seed' hwf hnd
    hnofb hseed (fun t => envs.getD (T - 1 - t) (fun _ => 0)) T ⟨st0, mems, kids⟩ envs hrun ?_ ?_
  · intro j hj
    have hj' : j < envs.length := by rw [hlenE]; exact hj
    show envs[j]? = some (envs.getD (T - 1 - (T - 1 - j)) (fun _ => 0))
    rw [show T - 1 - (T - 1 - j) = j by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj']
    rfl
  · intro mn iname conns hm
    obtain ⟨args, outs, mc, hcall, hmc, hne, hall⟩ := gInsts _ hm rfl
    obtain ⟨outWs, argWs, iname', hout, hargsW, _, _, hfields, hfnd, _, _, _, _, _, heq⟩ := hcall
    injection heq with h1 h2 h3
    subst h1; subst h2; subst h3
    refine ⟨mc, Sparkle.IR.RegDedup.declWidth mc, ?_⟩
    have hcm : childMap dsn.modules mc.name = some (mc, Sparkle.IR.RegDedup.declWidth mc) := by
      simp [childMap, hmc]
    -- the reset and the clock are never assigned: every environment holds the seed's
    have hfix : ∀ x, x ∉ insNames → (∀ t st, seed t st x = 0) → (∀ r, Stmt.assign x r ∉ m.body) →
        ∀ t, envs.getD (T - 1 - t) (fun _ => 0) x = 0 := by
      intro x hxi hx0 hna t
      rw [List.getD_eq_getElem?_getD]
      cases hj : envs[T - 1 - t]? with
      | none => rfl
      | some e =>
        have hjl : T - 1 - t < envs.length := (List.getElem?_eq_some_iff.mp hj).1
        obtain ⟨stj, memsj, hev⟩ := henvs (T - 1 - t) hjl
        have he : envs[T - 1 - t] = e := (List.getElem?_eq_some_iff.mp hj).2
        rw [he] at hev
        have hnt : x ∉ assignTargets m.body := by
          intro hx
          obtain ⟨r, hr⟩ := mem_assignTargets m.body x hx
          exact hna r hr
        rw [Option.getD_some, evalAssigns_assignFrame (weOf m) memsj (childMap dsn.modules) m.body
          _ _ x hwf hev hnt, hoff _ _ x hxi]
        exact hx0 _ _
    obtain ⟨cenvs, hcrun, hcobs⟩ := hchild args outs mc iname argWs outWs hargsW hout hmc hm
      hne hfnd hfields hall (fun t => envs.getD (T - 1 - t) (fun _ => 0))
      (hfix "rst" rstNot hrst (fun r => (hnoCR r).1))
      (hfix "clk" clkNot hclk0 (fun r => (hnoCR r).2))
      (by
        intro t ht q hq w g hw hg hql
        have hjt : T - 1 - t < envs.length := by rw [hlenE]; omega
        show envs.getD (T - 1 - t) _ w = g (T - 1 - t)
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjt, Option.getD_some]
        obtain ⟨_, hgetA⟩ := Tools.ShippingMachineInst.mapM_some _ args argWs hargsW
        obtain ⟨w', hw', hwq⟩ := hgetA q hq
        rw [hw] at hwq; cases hwq
        have hlw : lets[args[q]]? = some w := by
          rw [hlets, List.getElem?_drop, ← hw']
          congr 1
          rw [hallLen]; omega
        exact hletobs (T - 1 - t) hjt (args[q]) w g hlw hg hql)
      (by
        intro t ht idx e w he hw
        have hjt : T - 1 - t < envs.length := by rw [hlenE]; omega
        show envs.getD (T - 1 - t) _ w = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjt, Option.getD_some]
        obtain ⟨_, hgetO⟩ := Tools.ShippingMachineInst.mapM_some _ outs outWs hout
        have hidx : idx < outs.length := (List.getElem?_eq_some_iff.mp he).1
        obtain ⟨w', hw', hwi⟩ := hgetO idx hidx
        rw [hw] at hwi; cases hwi
        have he' : outs[idx] = e := by
          rw [List.getElem?_eq_getElem hidx] at he; exact Option.some.inj he
        rw [he'] at hw'
        have hkI : e.1 < d.shape.insts.length := by
          have := (hall e (by rw [← he']; exact List.getElem_mem hidx)).1
          have := (List.getElem?_eq_some_iff.mp this).1
          simpa using this
        have hw2 : names[machNIn d.shape + e.1]? = some w := by
          obtain ⟨k, f⟩ := e; exact hw'
        have hwk' : insNames[e.1]? = some w := by rw [← hinsAt e.1 hkI]; exact hw2
        obtain ⟨p, hp⟩ : ∃ p, insP[e.1]? = some p :=
          ⟨_, List.getElem?_eq_getElem (by rw [hinsLen]; exact hkI)⟩
        have hpw : p.name = w := by
          have : insNames[e.1]? = some p.name := by simp [insNames, hp]
          rw [hwk'] at this; exact (Option.some.inj this).symm
        obtain ⟨stj, memsj, hev⟩ := henvs (T - 1 - t) hjt
        have hwout : w ∈ bodyInstOuts (childMap dsn.modules) m.body := by
          have := portOut e.1 hkI
          rw [hwk'] at this
          obtain ⟨n', hn', hnn⟩ := List.mem_map.mp this
          cases hnn; exact hn'
        have hframe := evalAssigns_frame (weOf m) memsj (childMap dsn.modules) m.body _ _ w hwf hev
          (instOuts_not_written m.body w hwf hwout)
        rw [hframe, ← hpw, hon _ stj e.1 p hp, show T - 1 - (T - 1 - t) = t by omega])
    exact ⟨cenvs, hcm, hcrun, hcobs⟩

/-- `machine_linkedTG_of` for the endpoint's ids. -/
theorem machine_linkedTG {σ : Type} (KS : KStep σ) (hloc : KSLocal KS) {declName : Name} {d : MachineData} {m : Module} {dsn : Design}
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
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length) :
    ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
    ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
      regs.Nodup ∧ regs.length = d.ss.length ∧
      ∃ lets : List String, lets.length = d.letBs.length ∧
      MachineWired declName d.shape ids cache m dsn regs lets ∧
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
        -- every instance's child, on the source's argument and call values
        (∀ (args : List Nat) (outs : List (Nat × String)) (mc : Module) (iname : String)
            (argWs outWs : List String),
          args.mapM (fun j => ((machPorts declName ids cache d.shape.binders).map (·.name))[
            machNIn d.shape + d.shape.insts.length + d.shape.layout.slots.length + j]?) =
            some argWs →
          outs.mapM (fun (k, _) => ((machPorts declName ids cache d.shape.binders).map (·.name))[
            machNIn d.shape + k]?) = some outWs →
          moduleByName dsn.modules mc.name = some mc →
          Stmt.inst mc.name iname (connsG mc argWs outs outWs) ∈ m.body →
          outs ≠ [] → (outs.map (·.2)).Nodup →
          (outs.map (·.2)).all (fun f => mc.outputs.any (·.name == f)) = true →
          (∀ e ∈ outs, (d.shape.insts.map (·.2.1))[e.1]? = some args ∧
            d.shape.instFields.getD e.1 "" = e.2 ∧
            ∀ c md, (d.shape.insts.map (·.1))[e.1]? = some c →
              (d.shape.instOrigins.getD e.1 .ord).child? = some md → mc = md.1) →
          ∀ Pw : Nat → Env,
            (∀ t, Pw t "rst" = 0) → (∀ t, Pw t "clk" = 0) →
            (∀ t, t < T → ∀ (q : Nat) (hq : q < args.length) (w : String) (g : Nat → Nat),
              argWs[q]? = some w → (lsrc i bools bits)[args[q]]? = some g → args[q] < d.ls.length →
              Pw t w = g (T - 1 - t)) →
            (∀ t, t < T → ∀ (idx : Nat) (e : Nat × String) (w : String), outs[idx]? = some e →
              outWs[idx]? = some w →
              Pw t w = posEnc (fun p => (extB i bools bits p).val (T - 1 - t))
                (fun p n => (ext i bools bits p n).val (T - 1 - t)) (kD + e.1)
                (((d.bsIn.drop kD)[e.1]?.map (·.2)).getD .domain)) →
            ∃ cenvs, runKS KS mc (Sparkle.IR.RegDedup.declWidth mc)
                (inConns mc.outputs (connsG mc argWs outs outWs)) Pw T (kids iname) = some cenvs ∧
              ∀ j, j < T → ∀ p ∈ mc.outputs, ∀ w,
                (connsG mc argWs outs outWs).lookup p.name = some (.ref w) →
                (cenvs[j]?).map (· p.name) = some (Pw (T - 1 - j) w)) →
        ∃ envs, runModuleTG KS (weOf m) (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ =
            some envs ∧
          envs.length = T ∧
          ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
            d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
            (envs[j]'hj) o.name = f j := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, trace⟩ := h
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired,
    machine_linkedTG_of KS hloc nd len rnd rlen llen wired trace hfe kD hkD hI hIlen hSL hSlen hLlen hNIn⟩


end Tools.ShippingMachineLinkedTG
