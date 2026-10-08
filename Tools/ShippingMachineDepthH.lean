import Tools.ShippingMachineShipsHierH
import Tools.ShippingHierSVRunH
import Tools.ShippingMachineDepthRun
import Tools.ShippingMachineShipsComb

/-! # Children with combinational children, at depth

A sequential child may itself call combinational children (`closeInsts`:
`wKeccakF` calls the round-constant table). Its composed theorem
(`f.machine_composed`, `ComposedH`) states the combinational linked run
`runModuleH`; the depth composition (`ComposedNW`) wants the stateful run
`runModuleTG (KSn _ 0)`, where each instance steps its child by `flatKS`
(`stepModule` on the connection-fed, state-backed environment). For children
that are assignments only, compute from their input ports and have every input
connected by a wire (`kidsComb`), the two runs coincide (`runModuleTG_flat_of_H`).
The composed theorem's premise about each call's module is discharged from a
boundary that names no wiring (`BoundH`: every instance module of the body
satisfies the premise of each call) — true when the calls are of one child,
as in `wKeccakF`. Then `composedNW0_of_H` is the child's composed theorem at
depth 0. -/
namespace Tools.ShippingMachineDepthH
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (declWidth isAssign)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierState
open Tools.ShippingHierStateG Tools.ShippingMachineLinked Tools.ShippingHierOptRunH
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingHierSVRunH (lookup_inConns bindOuts_congr)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- Decidable: every instance's child is assignments only, computes its
outputs from its input ports, and has every input connected by a wire. -/
def kidsComb (ms : List Sparkle.IR.AST.Module) (body : List Stmt) : Bool :=
  body.all fun st => match st with
    | .inst mn _ conns => match moduleByName ms mn with
      | some c => c.body.all isAssign &&
          readsClosed (c.inputs.map (·.name)) c.body &&
          c.outputs.all (fun p => (writesOf c.body).contains p.name) &&
          c.outputs.all (fun p => !(c.inputs.map (·.name)).contains p.name) &&
          c.inputs.all (fun p => match conns.lookup p.name with
            | some (.ref _) => true
            | _ => false)
      | none => false
    | _ => true

theorem memFree_of_assigns : ∀ {body : List Stmt}, body.all isAssign = true →
    Tools.ConeFold.memFree body
  | [], _ => trivial
  | st :: rest, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ih := memFree_of_assigns (body := rest) h.2
    cases st <;> simp_all [Tools.ConeFold.memFree, isAssign]

/-- **The linked fold with combinational children is the stateful fold with
`flatKS`**, the children's states unchanged. -/
theorem evalAssignsKG_flat_of_H (W : WEnv) (ms : List Sparkle.IR.AST.Module) (mems : MEnv)
    (kids : String → KidState) :
    ∀ (body : List Stmt) (env envF : Env) (acc : String → KidState),
      Tools.ConeFold.memFree body → kidsComb ms body = true →
      evalAssignsH W (childMap ms) mems body env = some envF →
      ∃ acc', evalAssignsKG flatKS W (childMap ms) kids mems body env acc = some (envF, acc')
  | [], env, envF, acc, _, _, h => by
    simp only [evalAssignsH, Option.some.injEq] at h
    subst h; exact ⟨acc, rfl⟩
  | st :: rest, env, envF, acc, hm, hloc, h => by
    have hm' : Tools.ConeFold.memFree rest := by
      cases st <;> simp_all [Tools.ConeFold.memFree]
    simp only [kidsComb, List.all_cons, Bool.and_eq_true] at hloc
    obtain ⟨hst, hrest⟩ := hloc
    have hrest' : kidsComb ms rest = true := hrest
    cases st with
    | assign l r =>
      simp only [evalAssignsH] at h
      cases hv : evalExpr W env r with
      | none => simp [hv] at h
      | some v =>
        simp only [hv, Option.bind_eq_bind, Option.bind_some] at h
        simp only [evalAssignsKG, hv, Option.bind_eq_bind, Option.bind_some]
        exact evalAssignsKG_flat_of_H W ms mems kids rest _ envF acc hm' hrest' h
    | register => exact evalAssignsKG_flat_of_H W ms mems kids rest env envF acc hm' hrest' h
    | memory => simp [Tools.ConeFold.memFree] at hm
    | inst mn iname conns =>
      cases hc : moduleByName ms mn with
      | none => simp [hc] at hst
      | some c =>
        simp only [hc, Bool.and_eq_true] at hst
        obtain ⟨⟨⟨⟨hasg, hcl⟩, hw⟩, hio⟩, hcon⟩ := hst
        have hC : childMap ms mn = some (c, declWidth c) := by simp [childMap, hc]
        simp only [evalAssignsH, hC, Option.bind_eq_bind, Option.bind_some] at h
        cases hE : evalAssigns (declWidth c) mems c.body (connEnv conns env) with
        | none => simp [hE] at h
        | some cres =>
          simp only [hE, Option.bind_some] at h
          have hmf := memFree_of_assigns hasg
          have hagree : ∀ n ∈ c.inputs.map (·.name),
              connEnv conns env n = connEnvS (inConns c.outputs conns) env (kids iname).st n := by
            intro n hn
            have hno : n ∉ c.outputs.map (·.name) := by
              intro hmo
              obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hmo
              have := List.all_eq_true.mp hio p hp
              simp [List.contains_eq_mem, hn] at this
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
            have hr := List.all_eq_true.mp hcon p hp
            simp only [connEnv, connEnvS, lookup_inConns hno conns]
            cases hl : conns.lookup p.name with
            | none => rw [hl] at hr; cases hr
            | some e =>
              cases e with
              | ref w => rfl
              | _ => rw [hl] at hr; cases hr
          obtain ⟨r2, hr2, hagr⟩ := evalAssigns_local _ mems c.body _ _ _ cres hmf hcl hagree hE
          have hr2' : evalAssigns (declWidth c) (kids iname).mems c.body
              (connEnvS (inConns c.outputs conns) env (kids iname).st) = some r2 := by
            rw [← Tools.ShippingHierSVRunH.evalAssigns_mems _ mems _ c.body _ hmf]; exact hr2
          have hbo : bindOuts c.outputs conns r2 env = bindOuts c.outputs conns cres env :=
            bindOuts_congr conns r2 cres c.outputs env (fun p hp => hagr p.name
              (List.mem_append_right _ (by
                have := List.all_eq_true.mp hw p hp
                simpa [List.contains_eq_mem] using this)))
          have hstep : flatKS c (declWidth c) (inConns c.outputs conns) env (kids iname) =
              some (r2, ⟨(kids iname).st, (kids iname).mems⟩) := by
            simp only [flatKS, stepModule, hr2', Option.bind_eq_bind, Option.bind_some,
              Tools.ShippingMachineShipsComb.regNexts_assigns hasg,
              Tools.ShippingMachineShipsComb.memNexts_assigns hasg, Option.map_some,
              Tools.ShippingMachineShipsComb.applyNexts_nil]
          simp only [evalAssignsKG, hC, hstep, Option.bind_eq_bind, Option.bind_some, hbo]
          exact evalAssignsKG_flat_of_H W ms mems kids rest _ envF _ hm' hrest' h

/-- **A combinational linked run is a `flatKS` stateful run**, from any
children's states. -/
theorem runModuleTG_flat_of_H (W : WEnv) (ms : List Sparkle.IR.AST.Module) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env)
    (hm : Tools.ConeFold.memFree body) (hloc : kidsComb ms body = true) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv) (kids : String → KidState) (envs : List Env),
      runModuleH W (childMap ms) body seed T st mems = some envs →
      runModuleTG flatKS W (childMap ms) body seed T ⟨st, mems, kids⟩ = some envs
  | 0, _, _, _, envs, h => by
    simp only [runModuleH, Option.some.injEq] at h; subst h; rfl
  | k + 1, st, mems, kids, envs, h => by
    simp only [runModuleH] at h
    cases hS : stepModuleH W (childMap ms) body (seed k st) mems with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, nexts, mems', hF, hN, hM, rfl⟩ := stepModuleH_some hS
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleH W (childMap ms) body seed k (applyNexts st nexts) mems' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    obtain ⟨kids', hK⟩ := evalAssignsKG_flat_of_H W ms mems kids body _ envF kids hm hloc hF
    simp only [runModuleTG, stepModuleTG, hK, hN, hM, Option.bind_eq_bind, Option.bind_some]
    rw [runModuleTG_flat_of_H W ms body seed hm hloc k _ mems' kids' rest hR]
    rfl

/-- The calls' premise, without the wiring: every instance module of the
body satisfies the premise of every call (true when the calls are of one
child). -/
def BoundH (R : Nat → Sparkle.IR.AST.Module → Prop) (d : MachineData) (m : Sparkle.IR.AST.Module) (dsn : Design) : Prop :=
  ∀ k mc, k < d.shape.insts.length → moduleByName dsn.modules mc.name = some mc →
    (∃ iname conns, Stmt.inst mc.name iname conns ∈ m.body) → R k mc

/-- **A machine with combinational children, composed at depth 0.** -/
theorem composedNW0_of_H {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    (hC : Tools.ShippingMachineShipsHierH.ComposedH R declName d kD m dsn dom src ext)
    (hB : BoundH R d m dsn) (hcomb : kidsComb dsn.modules m.body = true)
    (hwf : linkedWF (childMap dsn.modules) m.body = true) :
    Tools.ShippingMachineDepthRun.ComposedNW 0 declName d kD m dsn dom src ext
      (fun _ bools _ => bools) := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩ := hC
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems kids hsrc hpass hrst _ hinit _
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T seed st0 mems hsrc hpass hrst hinit
    (fun k args mc st hk hst hcall hmc => by
      apply hB k mc _ hmc
      · obtain ⟨_, _, _, iname, _, _, _, _, _, _, _, _, _, heq⟩ := hcall
        subst heq
        exact ⟨_, _, hst⟩
      · have := (List.getElem?_eq_some_iff.mp hk).1
        simpa using this)
  refine ⟨envs, ?_, hlen, hobs⟩
  exact runModuleTG_flat_of_H _ dsn.modules m.body seed
    (Tools.ShippingHierOptRun.memFree_of_linkedWF _ hwf) hcomb T st0 mems kids envs hrun

/-- The run boundary of such a child: the calls' premise without the wiring,
and the decidable facts about its children and body. -/
def BndH (R : Nat → Sparkle.IR.AST.Module → Prop) (d : MachineData)
    (m : Sparkle.IR.AST.Module) (dsn : Design) : Prop :=
  BoundH R d m dsn ∧ kidsComb dsn.modules m.body = true ∧
    linkedWF (childMap dsn.modules) m.body = true

/-- `composedNW0_of_H` at every run of the core entry: the form
`seqChildRunN_of_composed` takes. -/
theorem composedN0_of_H {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name}
    {d : MachineData} {kD : Nat} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      Tools.ShippingEntrySoundness.RunsTo (synthesizeCombinationalCore declName [] false)
        mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      Tools.ShippingMachineShipsHierH.ComposedH R declName d kD m design dom src ext) :
    ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      Tools.ShippingEntrySoundness.RunsTo (synthesizeCombinationalCore declName [] false)
        mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      BndH R d m design →
      Tools.ShippingMachineDepthRun.ComposedNW 0 declName d kD m design dom src ext
        (fun _ bools _ => bools) := by
  intro mctx mref cctx cref w w' m design hr entry closes hB
  exact composedNW0_of_H (composed hr entry closes) hB.1 hB.2.1 hB.2.2

end Tools.ShippingMachineDepthH
