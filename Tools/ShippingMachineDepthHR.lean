import Tools.ShippingMachineDepthH
import Tools.ShippingMachineComposeR
import Tools.ShippingMachineDepthRunR
import Tools.ShippingChildCache

/-! # A child with one-output combinational calls, at depth 0, the boundary derived

`composedN0_of_H` turns a combinational parent's composed theorem into the
depth-0 form a parent of it composes, given `BndH` — the calls' premise and
`kidsComb` of the run. With the derived composed theorem
(`machine_composedR`: no calls' premise, `ChildSynthIs` and reflection facts
in the run's contexts), `BoundH` is trivial, and `kidsComb` of the run comes
from the run itself: its closing CHECKS it (`kidsCombB`, `closeInsts_kidsComb`). -/
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

theorem readsClosedB_eq : ∀ (S : List String) (body : List Stmt),
    readsClosedB S body = Tools.ShippingHierOptRunH.readsClosed S body
  | _, [] => rfl
  | S, st :: rest => by
    simp only [readsClosedB, Tools.ShippingHierOptRunH.readsClosed, readsClosedB_eq]

theorem kidsComb_of_B {ms : List Sparkle.IR.AST.Module} {body : List Stmt} (h : kidsCombB ms body = true) :
    Tools.ShippingMachineDepthH.kidsComb ms body = true := by
  unfold kidsCombB at h
  unfold Tools.ShippingMachineDepthH.kidsComb
  rw [List.all_eq_true] at h ⊢
  intro st hst
  have := h st hst
  cases st with
  | inst mn iname conns =>
    simp only [readsClosedB_eq] at this
    exact this
  | _ => rfl

/-- **A one-output combinational parent at depth 0, the run boundary derived.** -/
theorem composedN0_of_HR {declName : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    (Rest : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    (hsimple : d.shape.instFields = []) (hi : d.shape.insts ≠ [])
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      Tools.ShippingChildSynth.ChildSynthIs mctx mref cctx cref ∧ Rest mctx mref cctx cref →
      Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) declName d kD m design dom src ext) :
    ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      Tools.ShippingChildSynth.ChildSynthIs mctx mref cctx cref ∧ Rest mctx mref cctx cref →
      Tools.ShippingMachineDepthRun.ComposedNW 0 declName d kD m design dom src ext
        (fun _ bools _ => bools) := by
  intro mctx mref cctx cref w w' m design hr entry closes hb
  have hC := composed hr entry closes hb
  obtain ⟨t, t', d₀, children, _, hcc, _⟩ :=
    Tools.ShippingChildSynth.machine_children_real hr entry closes hb.1 hi
  have hcomb : Tools.ShippingMachineDepthH.kidsComb design.modules m.body = true := by
    rcases hcc with ⟨_, h⟩ | ⟨hfe, _, _⟩
    · exact kidsComb_of_B (Tools.ShippingChildServe.closeInsts_kidsComb h)
    · exact absurd hsimple hfe
  exact Tools.ShippingMachineDepthH.composedNW0_of_H hC
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) hcomb

/-- **At every depth an assignment-only child steps by its assignments**, its
outputs those of the combinational step. -/
theorem KSn_assigns_step (children : String → Option (Sparkle.IR.AST.Module × WEnv)) :
    ∀ (n : Nat) (c : Sparkle.IR.AST.Module) (cwe : WEnv) (cin : List (String × Sparkle.IR.AST.Expr))
      (env : Env) (s : KT n) {r : Env}, c.body.all isAssign = true →
      evalAssigns cwe (memsOf n s) c.body (connEnvS cin env (stOf n s)) = some r →
      ∃ s', KSn children n c cwe cin env s = some (r, s')
  | 0, c, cwe, cin, env, s, r, hasg, h => by
    refine ⟨⟨KidState.st s, KidState.mems s⟩, ?_⟩
    have h' : evalAssigns cwe (KidState.mems s) c.body (connEnvS cin env (KidState.st s)) = some r := h
    simp only [KSn, flatKS, stepModule, h', Option.bind_eq_bind, Option.bind_some,
      Tools.ShippingMachineShipsComb.regNexts_assigns hasg,
      Tools.ShippingMachineShipsComb.memNexts_assigns hasg, Option.map_some,
      Tools.ShippingMachineShipsComb.applyNexts_nil]
    rfl
  | n + 1, c, cwe, cin, env, s, r, hasg, h => by
    have hf : instFree c.body := by
      intro st hst
      have := List.all_eq_true.mp hasg st hst
      cases st <;> simp_all [isAssign, Sparkle.IR.Machine.isInst]
    refine ⟨⟨KState.st s, KState.mems s, KState.kids s⟩, ?_⟩
    show stepModuleTG (KSn children n) cwe children c.body (connEnvS cin env (KState.st s)) s = _
    have h' : evalAssigns cwe s.mems c.body (connEnvS cin env s.st) = some r := h
    simp only [stepModuleTG, evalAssignsKG_instFree _ cwe children s.kids s.mems c.body _ _ hf,
      h', Option.map_some, Option.bind_eq_bind, Option.bind_some,
      Tools.ShippingMachineShipsComb.regNexts_assigns hasg,
      Tools.ShippingMachineShipsComb.memNexts_assigns hasg,
      Tools.ShippingMachineShipsComb.applyNexts_nil]
    rfl

theorem evalAssignsKG_KSn_of_H (D0 : Nat) (W : WEnv) (ms : List Sparkle.IR.AST.Module) (mems : MEnv)
    (kids : String → KT D0) :
    ∀ (body : List Stmt) (env envF : Env) (acc : String → KT D0),
      Tools.ConeFold.memFree body → kidsComb ms body = true →
      evalAssignsH W (childMap ms) mems body env = some envF →
      ∃ acc', evalAssignsKG (KSn (childMap ms) D0) W (childMap ms) kids mems body env acc = some (envF, acc')
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
        exact evalAssignsKG_KSn_of_H D0 W ms mems kids rest _ envF acc hm' hrest' h
    | register => exact evalAssignsKG_KSn_of_H D0 W ms mems kids rest env envF acc hm' hrest' h
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
              connEnv conns env n = connEnvS (inConns c.outputs conns) env (stOf D0 (kids iname)) n := by
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
          have hr2' : evalAssigns (declWidth c) (memsOf D0 (kids iname)) c.body
              (connEnvS (inConns c.outputs conns) env (stOf D0 (kids iname))) = some r2 := by
            rw [← Tools.ShippingHierSVRunH.evalAssigns_mems _ mems _ c.body _ hmf]; exact hr2
          have hbo : bindOuts c.outputs conns r2 env = bindOuts c.outputs conns cres env :=
            bindOuts_congr conns r2 cres c.outputs env (fun p hp => hagr p.name
              (List.mem_append_right _ (by
                have := List.all_eq_true.mp hw p hp
                simpa [List.contains_eq_mem] using this)))
          obtain ⟨s', hstep⟩ := KSn_assigns_step (childMap ms) D0 c (declWidth c) (inConns c.outputs conns)
            env (kids iname) hasg hr2'
          simp only [evalAssignsKG, hC, hstep, Option.bind_eq_bind, Option.bind_some, hbo]
          exact evalAssignsKG_KSn_of_H D0 W ms mems kids rest _ envF _ hm' hrest' h

theorem runModuleTG_KSn_of_H (n : Nat) (W : WEnv) (ms : List Sparkle.IR.AST.Module) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env)
    (hm : Tools.ConeFold.memFree body) (hloc : kidsComb ms body = true) :
    ∀ (T : Nat) (st : String → Nat) (mems : MEnv) (kids : String → KT n) (envs : List Env),
      runModuleH W (childMap ms) body seed T st mems = some envs →
      runModuleTG (KSn (childMap ms) n) W (childMap ms) body seed T ⟨st, mems, kids⟩ = some envs
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
    obtain ⟨kids', hK⟩ := evalAssignsKG_KSn_of_H n W ms mems kids body _ envF kids hm hloc hF
    simp only [runModuleTG, stepModuleTG, hK, hN, hM, Option.bind_eq_bind, Option.bind_some]
    rw [runModuleTG_KSn_of_H n W ms body seed hm hloc k _ mems' kids' rest hR]
    rfl

theorem composedNWn_of_H (n : Nat) {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    (hC : Tools.ShippingMachineShipsHierH.ComposedH R declName d kD m dsn dom src ext)
    (hB : BoundH R declName d m dsn) (hcomb : kidsComb dsn.modules m.body = true) :
    Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext
      (fun _ bools _ => bools) := by
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

/-- **A one-output combinational parent at ANY depth, the run boundary derived.**
Depth is an upper bound: a parent whose children are combinational runs the
same at every depth (`composedNWn_of_H`), so a shallow subtree may sit under a
deeper parent. -/
theorem composedNn_of_HR (n : Nat) {declName : Name} {d : MachineData} {kD : Nat} {ι : Type}
    {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    (Rest : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    (hsimple : d.shape.instFields = []) (hi : d.shape.insts ≠ [])
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      (Tools.ShippingChildCache.RefIs mctx mref cctx cref ∧
        Tools.ShippingChildCache.CacheReads mctx mref cctx cref) ∧ Rest mctx mref cctx cref →
      Tools.ShippingMachineShipsHierH.ComposedH (fun _ _ => True) declName d kD m design dom src ext) :
    ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      MachineCloses mctx mref cctx cref declName d.shape →
      (Tools.ShippingChildCache.RefIs mctx mref cctx cref ∧
        Tools.ShippingChildCache.CacheReads mctx mref cctx cref) ∧ Rest mctx mref cctx cref →
      Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m design dom src ext
        (fun _ bools _ => bools) := by
  intro mctx mref cctx cref w w' m design hr entry closes hb
  have hC := composed hr entry closes hb
  obtain ⟨t, t', d₀, children, _, hcc, _⟩ :=
    Tools.ShippingChildSynth.machine_children_real hr entry closes
      (Tools.ShippingChildCache.childSynthIs_of hb.1.1 hb.1.2) hi
  have hcomb : Tools.ShippingMachineDepthH.kidsComb design.modules m.body = true := by
    rcases hcc with ⟨_, h⟩ | ⟨hfe, _, _⟩
    · exact kidsComb_of_B (Tools.ShippingChildServe.closeInsts_kidsComb h)
    · exact absurd hsimple hfe
  exact composedNWn_of_H n hC (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) hcomb

end Tools.ShippingMachineDepthHR
