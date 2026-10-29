import Tools.ShippingMachineCompose
import Tools.ShippingMachineShipsHierH
import Tools.ShippingMachineDepthHR

/-! # The composed theorems with the Bool input reader as a parameter (`extB`)

S4 consumer freeze rev2 (scripts/gen2/S4_CONSUMER_FREEZE.md, approved at 4ff583e9), §2.1-§2.4.
`ComposedH`, `machine_linked_of` and `composedNWn_of_H` read a Bool input signal as `bools j`
(the identity `extB := fun _ bools _ => bools`); the package trace reads it as `p.extBS`. Each
declaration below is the ACCEPTED text (ShipsHierH.lean:33-65, Compose.lean:538-799,
DepthHR.lean:208-230) with ONE new binder `extB` right after `ext` (same implicitness as `ext`)
and every `(bools x).val` read of an input signal replaced by `(extB i bools bits x).val`;
nothing else changes. The proofs are copied, with the `let V` of `machine_linked_of`
(Compose.lean:671-673) reading `extB`. Each copy is placed by REOPENING the original namespace
with the original file's `open`s verbatim.

Identity checks: `composedHB_id` (`rfl`), `machine_linked_of_viaB` (the accepted statement of
`machine_linked_of`, reproduced verbatim, proved by `machine_linked_ofB` at the identity) and the
`example` after `composedNWn_of_HB` (the accepted premise and conclusion of `composedNWn_of_H`).
Existing declarations are unchanged. -/

namespace Tools.ShippingMachineShipsHierH
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierOpen Tools.ShippingHierState
open Tools.ShippingHierOptRun Tools.ShippingHierOptRunH
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMachineShipping
open Tools.ShippingMachineLinked Tools.ShippingMachineShipsHier
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- `ComposedH` with the Bool input reader `extB` as a parameter. -/
def ComposedHB (R : Nat → Sparkle.IR.AST.Module → Prop) (declName : Name) (d : MachineData) (kD : Nat)
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
    ∃ lets : List String, lets.length = d.letBs.length ∧
    MachineWired declName d.shape ids cache m dsn regs lets ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t)) (fun j n => (ext i bools bits j n).val (T - 1 - t))
        (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
        Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
          d.shape.layout.slots.length
          ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
        moduleByName dsn.modules mc.name = some mc →
        R k mc) →
      ∃ envs, runModuleH (weOf m) (childMap dsn.modules) m.body seed T st0 mems = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j

/-- CHECK 1: at the identity `extB` the copy IS the accepted definition (the only difference is the
β-redex `(fun _ bools _ => bools) i bools bits j`). -/
theorem composedHB_id (R : Nat → Sparkle.IR.AST.Module → Prop) (declName : Name) (d : MachineData) (kD : Nat)
    (m : Sparkle.IR.AST.Module) (dsn : Design) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) :
    ComposedHB R declName d kD m dsn dom src ext (fun _ bools _ => bools) =
      ComposedH R declName d kD m dsn dom src ext := rfl

end Tools.ShippingMachineShipsHierH

namespace Tools.ShippingMachineCompose
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf writesOf stmtWrites)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked

section LinkedB
open Lean Sparkle.Compiler.Elab Tools.ShippingMachineEntry Tools.ShippingMixedEntrySoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMachineAuto
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine (SlotField OutField)
open Tools.ShippingEntrySoundness (weOf)

/-- `machine_linked_of` with the Bool input reader `extB` as a parameter (the trace, the
premises and the call values read `extB i bools bits`). -/
theorem machine_linked_ofB {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module} {dsn : Design}
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
    (hsimple : d.shape.instFields = [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (P : Nat → List Nat → Prop) (F : Nat → List Nat → Nat) :
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t)) (fun j n => (ext i bools bits j n).val (T - 1 - t))
        (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      -- every call's module computes `F k`
      (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
        Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
          d.shape.layout.slots.length
          ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
        Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc →
        ChildFn mc (P k) (F k)) →
      -- and the source's call is `F k` of its arguments
      (∀ k args j, (d.shape.insts.map (·.2.1))[k]? = some args → j < T →
        (∀ q ∈ args, q < d.ls.length ∧ q < (lsrc i bools bits).length) ∧
        P k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) ∧
        F k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) =
          posEnc (fun p => (extB i bools bits p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
            (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)) →
      ∃ envs, runModuleH (weOf m) (childMap dsn.modules) m.body seed T st0 mems = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j := by
  intro i bools bits T seed st0 mems hin hpass hrst hinit hchild hval
  obtain ⟨nnd, alloc, regsIn, hlets, calls, insts, link, _, _, _⟩ := wired
  have calls := calls hsimple
  have insts := insts hsimple
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
      List.getElem?_append_left (by simp [insNames, hinsLen, hDlen]; omega)]
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
  -- the linked run
  have hwf : linkedWF (childMap dsn.modules) m.body = true := by
    rw [← linkedOk_eq]; exact link
  have hoff' : ∀ t st n, n ∉ bodyInstOuts (childMap dsn.modules) m.body →
      seed' t st n = seed t st n := by
    intro t st n hn
    apply hoff
    intro hni
    obtain ⟨k, hk, hkn⟩ := List.getElem_of_mem hni
    have hk' : k < d.shape.insts.length := by simp [insNames, hinsLen] at hk; exact hk
    obtain ⟨args, mc, st', _, hst', hmc, hcall⟩ := calls k hk'
    exact hn (callStmt_out hst' hcall hmc (by rw [hinsAt k hk', List.getElem?_eq_getElem hk, hkn]))
  obtain ⟨_, henvs⟩ := runModule_envs (weOf m) m.body seed' T st0 mems envs hrun
  refine ⟨envs, runModuleH_of_run (weOf m) (childMap dsn.modules) m.body seed seed' hwf hoff'
    T st0 mems envs hrun ?_, hlenE, hobs⟩
  intro j hj mems' mn iname conns hmem
  obtain ⟨k, args, mc, hargs, hmc, hcall⟩ := insts mn iname conns hmem
  have hname : mc.name = mn := Tools.ShippingMachineInst.moduleByName_name hmc
  have hmc' : Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc := by
    rw [hname]; exact hmc
  have hjT : j < T := by omega
  obtain ⟨hq, hP, hF⟩ := hval k args j hargs hjT
  refine childComputes_of_call hmc hcall (hchild k args mc _ hargs hmem hcall hmc') ?_
  intro outW argWs hout hargWs
  -- the argument wires are the `let` wires of the arguments
  have hkI : k < d.shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
  have hargVals : argWs.map (envs[j]'hj) =
      args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0 := by
    obtain ⟨hl, hget⟩ := Tools.ShippingMachineInst.mapM_some _ args argWs hargWs
    apply List.ext_getElem (by simp [hl])
    intro q h1 h2
    have hqa : q < args.length := by simpa using h2
    have hqw : q < argWs.length := by simpa using h1
    simp only [List.getElem_map]
    obtain ⟨w, hw, hwq⟩ := hget q hqa
    have hwq' : argWs[q] = w := by
      rw [List.getElem?_eq_getElem hqw] at hwq; exact Option.some.inj hwq
    rw [hwq']
    obtain ⟨hql, hqs⟩ := hq (args[q]'hqa) (List.getElem_mem _)
    -- `w` is `let` wire `args[q]`
    have hlw : lets[args[q]'hqa]? = some w := by
      rw [hlets, List.getElem?_drop]
      rw [← hw]
      congr 1
      rw [hallLen]; omega
    obtain ⟨g, hg⟩ : ∃ g, (lsrc i bools bits)[args[q]'hqa]? = some g :=
      ⟨_, List.getElem?_eq_getElem hqs⟩
    rw [hletobs j hj (args[q]'hqa) w g hlw hg hql, hg]
    rfl
  have hout' : outW = insNames[k]'(by simp [insNames, hinsLen]; exact hkI) := by
    rw [hinsAt k hkI, List.getElem?_eq_getElem (by simp [insNames, hinsLen]; exact hkI)] at hout
    exact (Option.some.inj hout).symm
  -- the call's wire carries the call's value: the open run leaves it as seeded
  obtain ⟨stj, memsj, hev⟩ := henvs j hj
  have hframe := evalAssigns_frame (weOf m) memsj (childMap dsn.modules) m.body _ _ outW hwf hev
    (instOuts_not_written m.body outW hwf (by
      rw [hout']
      obtain ⟨args', mc', st', _, hst', hmc'', hcall'⟩ := calls k hkI
      exact callStmt_out hst' hcall' hmc'' (by
        rw [hinsAt k hkI, List.getElem?_eq_getElem (by simp [insNames, hinsLen]; exact hkI)])))
  have hpk : insP[k]? = some (insP[k]'(by rw [hinsLen]; exact hkI)) :=
    List.getElem?_eq_getElem _
  have hseedv := hon (T - 1 - j) stj k _ hpk
  refine ⟨by rw [hargVals]; exact hP, ?_⟩
  rw [hargVals, hF, hframe, hout']
  simp only [insNames, List.getElem_map]
  rw [hseedv]
  have : T - 1 - (T - 1 - j) = j := by omega
  rw [this]

/-- CHECK 2: the accepted theorem is the copy at the identity `extB`. The statement is
`machine_linked_of`'s (Compose.lean:538-607) reproduced verbatim. -/
theorem machine_linked_of_viaB {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module} {dsn : Design}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
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
        (fun j => (bools j).val (T - 1 - t))
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
    (hsimple : d.shape.instFields = [])
    (kD : Nat) (hkD : kD ≤ d.bsIn.length)
    (hI : ∀ b ∈ d.bsIn.drop kD, b.2 ≠ .domain)
    (hIlen : (d.bsIn.drop kD).length = d.shape.insts.length)
    (hSL : ∀ b ∈ d.slotBs ++ d.letBs, b.2 ≠ .domain)
    (hSlen : d.slotBs.length = d.shape.layout.slots.length)
    (hLlen : d.letBs.length = d.shape.layout.lets)
    (hNIn : machNIn d.shape = ((d.bsIn.take kD).filter (fun b => b.2 != .domain)).length)
    (P : Nat → List Nat → Prop) (F : Nat → List Nat → Nat) :
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv),
      (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
        (fun j => (bools j).val (T - 1 - t)) (fun j n => (ext i bools bits j n).val (T - 1 - t))
        (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      -- every call's module computes `F k`
      (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
        Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
          d.shape.layout.slots.length
          ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
        Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc →
        ChildFn mc (P k) (F k)) →
      -- and the source's call is `F k` of its arguments
      (∀ k args j, (d.shape.insts.map (·.2.1))[k]? = some args → j < T →
        (∀ q ∈ args, q < d.ls.length ∧ q < (lsrc i bools bits).length) ∧
        P k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) ∧
        F k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) =
          posEnc (fun p => (bools p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
            (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)) →
      ∃ envs, runModuleH (weOf m) (childMap dsn.modules) m.body seed T st0 mems = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j :=
  machine_linked_ofB (extB := fun _ bools _ => bools) nd len rnd rlen llen wired trace hsimple kD hkD hI hIlen
    hSL hSlen hLlen hNIn P F

end LinkedB
end Tools.ShippingMachineCompose

namespace Tools.ShippingMachineDepthHR
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingEntrySoundness
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierState
open Tools.ShippingHierStateG Tools.ShippingMachineLinked Tools.ShippingHierOptRunH
open Tools.ShippingMachineDepthH Tools.ShippingHierSVRunH
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (declWidth isAssign)

/-- `composedNWn_of_H` with the Bool input reader `extB` as a parameter. -/
theorem composedNWn_of_HB (n : Nat) {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (hC : Tools.ShippingMachineShipsHierH.ComposedHB R declName d kD m dsn dom src ext extB)
    (hB : BoundH R declName d m dsn) (hcomb : kidsComb dsn.modules m.body = true) :
    Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext
      extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩ := hC
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  -- the body's linked well-formedness: its wiring
  have hwf : linkedWF (childMap dsn.modules) m.body = true := by
    obtain ⟨_, _, _, _, _, _, hlink, _⟩ := wired
    rw [← Tools.ShippingMachineLinked.linkedOk_eq]; exact hlink
  intro i bools bits T seed st0 mems kids hsrc hpass hrst _ hinit _
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T seed st0 mems hsrc hpass hrst hinit
    (hB ids cache regs lets wired)
  refine ⟨envs, ?_, hlen, hobs⟩
  exact runModuleTG_KSn_of_H n _ dsn.modules m.body seed
    (Tools.ShippingHierOptRun.memFree_of_linkedWF _ hwf) hcomb T st0 mems kids envs hrun

/-- CHECK 3: at the identity `extB` the copy has the accepted conclusion and takes the accepted premise. -/
example (n : Nat) {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    (hC : Tools.ShippingMachineShipsHierH.ComposedH R declName d kD m dsn dom src ext)
    (hB : BoundH R declName d m dsn) (hcomb : kidsComb dsn.modules m.body = true) :
    Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext
      (fun _ bools _ => bools) :=
  composedNWn_of_HB n (extB := fun _ bools _ => bools)
    ((Tools.ShippingMachineShipsHierH.composedHB_id R declName d kD m dsn dom src ext).symm ▸ hC) hB hcomb

end Tools.ShippingMachineDepthHR
