import Tools.ShippingSrm6Sem
import Tools.ShippingDesignSVBounds
set_option autoImplicit false
-- UNBUILT (unit SRM11): see STATUS-SRM11.md for run names; the final-SHA rebuild is in REPORT-SRM11.md.
-- SCOPE (binding): the HEIGHT-INDEXED analogue of `Tools.ShippingDesignSVBounds.svBounds_of_checks`.  Where the uniform chain needs `designCheck C n o = true` (every kid checked at
-- the SAME depth, which a built memory module below depth 0 cannot satisfy), this file runs the same width-bound argument over `hcheck C rk f o = true` (SRM5) with `rk o.name = some r`, `r ≤ n + 1`.
-- PROVED here: `stepModuleTG_instFree`, `leafStepTG_bound` (a rank-0 module's cycle at any depth), `moduleStepBoundH`, `KSn_stepBoundH`, `runModuleTG_envBoundH`, `svBoundsH_of_checks`
-- (the premise `SVBoundsH` of SRM6's `design_sv_runH` from `hcheck`, bounded seeding, bounded start state and `InvN` of the instances), and the K2 relation `svBoundsH_of_svBounds`
-- (uniform `SVBounds` ⇒ `SVBoundsH` under `hcheck` and the rank facts).
-- PREMISES of `svBoundsH_of_checks` (named in its binders): `hcheck`, `hseedB` (top seeding maps bounded states to bounded environments), `hst` (bounded start state), `hkids` (`InvN` of every instance's state), the run.
-- NOT claimed: that `hseedB`/`hst`/`hkids` hold for the machine's actual run; the endpoint.  No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.
namespace Tools.ShippingSrm11Bounds
open Sparkle.IR.AST Sparkle.IR.Semantics Tools.ShippingDesignSV Tools.ShippingSrm5Height Tools.ShippingSrm6Sem
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierSVRun (oracle)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun
open Tools.ShippingDesignSVBounds
open Tools.ShippingHierarchySoundness (connEnvS)

/-- a flat module's cycle through the linked step is its flat cycle -/
theorem leafStepTG_bound {σ : Type} (KS : KStep σ) (C : String → Option (Module × WEnv)) {o : Module}
    (hl : leafCheck o = true) {env0 : Env} (hb0 : Bounded (weS o) env0) {s : KState σ}
    (hst : Bounded (weS o) s.st) {envF : Env} {s' : KState σ}
    (h : stepModuleTG KS (declWidth o) C o.body env0 s = some (envF, s')) :
    Bounded (weS o) envF ∧ Bounded (weS o) s'.st := by
  have hf := instFree_of_leafCheck hl
  unfold stepModuleTG at h
  rw [evalAssignsKG_instFree KS (declWidth o) C s.kids s.mems o.body _ _ hf] at h
  cases hE : evalAssigns (declWidth o) s.mems o.body env0 with
  | none => simp [hE] at h
  | some e1 =>
  cases hN : regNexts (declWidth o) s.mems o.body e1 with
  | none => simp [hE, hN] at h
  | some nexts =>
  cases hM : memNexts (declWidth o) o.body s.mems e1 with
  | none => simp [hE, hN, hM] at h
  | some mems' =>
  simp only [hE, hN, hM, Option.map_some, Option.bind_eq_bind, Option.bind_some, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hsm : stepModule (declWidth o) o.body env0 s.mems = some (e1, nexts, mems') := by
    simp only [stepModule, hE, hN, hM, Option.bind_eq_bind, Option.bind_some]
  obtain ⟨hbe, hnb⟩ := leaf_stepBound hl hb0 hsm
  exact ⟨hbe, applyNexts_bound hst hnb⟩

/-- The step bound at depth `m`, height-indexed: a child of rank `r ≤ m` passing `hcheck`, stepping by `KSn C m` from bounded inputs and a bounded state. -/
def StepBoundH (ms : List Module) (rk : String → Option Nat) (m : Nat) : Prop :=
  ∀ (child : Module) (f r : Nat), rk child.name = some r → r ≤ m →
    hcheck (Tools.ShippingMachineLinked.childMap ms) rk f child = true →
    ∀ (cin : List (String × Expr)) (env : Env) (s : KT m) (cres : Env) (s' : KT m),
      (∀ c ∈ cin, ∀ w, c.2 = .ref w → env w < 2 ^ weS child c.1) →
      InvN (Tools.ShippingMachineLinked.childMap ms) m child s →
      KSn (Tools.ShippingMachineLinked.childMap ms) m child (declWidth child) cin env s = some (cres, s') →
      Bounded (weS child) cres ∧ InvN (Tools.ShippingMachineLinked.childMap ms) m child s'

/-- **One cycle of a module of rank `r ≤ m + 1` passing `hcheck`, whose children step at depth `m`** (`moduleStepBound` over `hcheck`). -/
theorem moduleStepBoundH (ms : List Module) (rk : String → Option Nat) (m : Nat) (ih : StepBoundH ms rk m)
    {o : Module} {f r : Nat} (hr : rk o.name = some r) (hrm : r ≤ m + 1)
    (hchk : hcheck (Tools.ShippingMachineLinked.childMap ms) rk f o = true)
    {env0 : Env} (hb0 : Bounded (weS o) env0) {s : KState (KT m)} (hst : Bounded (weS o) s.st)
    (hkids : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
      Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
      InvN (Tools.ShippingMachineLinked.childMap ms) m gc (s.kids iname))
    {envF : Env} {s' : KState (KT m)}
    (h : stepModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) m) (declWidth o)
      (Tools.ShippingMachineLinked.childMap ms) o.body env0 s = some (envF, s')) :
    Bounded (weS o) envF ∧ Bounded (weS o) s'.st ∧
      ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
        Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
        InvN (Tools.ShippingMachineLinked.childMap ms) m gc (s'.kids iname) := by
  cases r with
  | zero =>
    have hl := hcheck_leaf hr hchk
    obtain ⟨h1, h2⟩ := leafStepTG_bound _ _ hl hb0 hst h
    refine ⟨h1, h2, ?_⟩
    intro mn iname conns gc gcwe hm
    have := instFree_of_leafCheck hl _ hm
    simp [Sparkle.IR.Machine.isInst] at this
  | succ h' =>
    obtain ⟨f', rfl⟩ := hcheck_fuel hr hchk
    obtain ⟨htxt, hedge⟩ := (hcheck_succ_iff hr f').mp hchk
    obtain ⟨hok, hsv, hwg, hwf, hnd, hns, hpm, hres⟩ := textCheckI_sound htxt
    have hkp : ∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
        Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
        ∃ r', rk gc.name = some r' ∧ r' ≤ m ∧ hcheck (Tools.ShippingMachineLinked.childMap ms) rk f' gc = true := by
      intro mn iname conns gc gcwe hm hc
      obtain ⟨child', cwe', r', hc', hrk, hle, hname, hkc⟩ := hedge mn iname conns hm
      rw [hc] at hc'; cases hc'
      exact ⟨r', by rw [hname]; exact hrk, by omega, hkc⟩
    unfold stepModuleTG at h
    cases hK : evalAssignsKG (KSn (Tools.ShippingMachineLinked.childMap ms) m) (declWidth o)
        (Tools.ShippingMachineLinked.childMap ms) s.kids s.mems o.body env0 s.kids with
    | none => simp [hK] at h
    | some ek =>
    obtain ⟨envF', kids'⟩ := ek
    cases hN : regNexts (declWidth o) s.mems o.body envF' with
    | none => simp [hK, hN] at h
    | some nexts =>
    cases hM : memNexts (declWidth o) o.body s.mems envF' with
    | none => simp [hK, hN, hM] at h
    | some mems' =>
    simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hgc : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ gc gcwe,
        Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) → ∀ e cr ks', Bounded (weS o) e →
        KSn (Tools.ShippingMachineLinked.childMap ms) m gc gcwe (inConns gc.outputs conns) e (s.kids iname) =
          some (cr, ks') →
        Bounded (weS gc) cr ∧ InvN (Tools.ShippingMachineLinked.childMap ms) m gc ks' := by
      intro mn iname conns hm gc gcwe hc e cr ks' hbe hk
      obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
      cases hxe
      obtain ⟨r', hrk', hle', hkc'⟩ := hkp mn iname conns gc _ hm hc
      refine ih gc f' r' hrk' hle' hkc' _ e (s.kids iname) cr ks' ?_
        (hkids mn iname conns gc _ hm hc) hk
      intro c hcin w hw
      have := hbe w
      rwa [hpm mn iname conns gc _ hm hc c (List.mem_filter.mp hcin).1 w hw] at this
    have hbF : Bounded (weS o) envF' :=
      evalAssignsKG_envBound (KSn (Tools.ShippingMachineLinked.childMap ms) m) (declWidth o) (weS o)
        (Tools.ShippingMachineLinked.childMap ms) s.kids s.mems o.body _ envF' s.kids kids' hok
        (fun l r hm e v hbe hv => assign_bound hsv hwg hm hbe hv)
        (fun mn iname conns hm gc gcwe hc e cr ks' hbe hk p hp w hl => by
          have h1 := (hgc mn iname conns hm gc gcwe hc e cr ks' hbe hk).1 p.name
          rwa [← hpm mn iname conns gc gcwe hm hc (p.name, .ref w)
            (Tools.ShippingHierSVRun.lookup_mem hl) w rfl] at h1)
        hb0 hK
    refine ⟨hbF, applyNexts_bound hst (regs_bound hok hwg hN), ?_⟩
    intro mn iname conns gc gcwe hm hc
    obtain ⟨gc', gcwe', envAt, cr, hc', hk, hag, -⟩ :=
      Tools.ShippingHierOptLinked.linked_consistentKG (KSn (Tools.ShippingMachineLinked.childMap ms) m)
        (declWidth o) (Tools.ShippingMachineLinked.childMap ms) s.kids s.mems
        o.body _ envF' s.kids kids' hwf hnd hK mn iname conns hm
    rw [hc] at hc'
    cases hc'
    have hloc := KSn_local (Tools.ShippingMachineLinked.childMap ms) m gc gcwe (inConns gc.outputs conns)
      envAt envF' (s.kids iname)
      (fun c hcin w hw => hag c (List.mem_filter.mp hcin).1 w hw
        (Tools.ShippingHierPremisesBase.noSelfRead_sound hns mn iname conns hm gc gcwe hc c hcin w hw))
    rw [hloc] at hk
    exact (hgc mn iname conns hm gc gcwe hc envF' cr (kids' iname) hbF hk).2

/-- **A child's step at any depth stays within the emitted widths, over `hcheck`.** -/
theorem KSn_stepBoundH (ms : List Module) (rk : String → Option Nat) : ∀ n, StepBoundH ms rk n
  | 0 => by
    intro child f r hr hrn hlc cin env s cres s' hin hinv hstep
    have hr0 : r = 0 := by omega
    subst hr0
    have hseed := connEnvS_bound hin hinv
    change (stepModule (declWidth child) child.body (connEnvS cin env (KidState.st s))
      (KidState.mems s)).map (fun r => (r.1, (⟨applyNexts (KidState.st s) r.2.1, r.2.2⟩ : KidState))) =
      some (cres, s') at hstep
    cases hsm : stepModule (declWidth child) child.body (connEnvS cin env (KidState.st s)) (KidState.mems s) with
    | none => rw [hsm] at hstep; cases hstep
    | some r =>
      obtain ⟨envF, nexts, mems'⟩ := r
      rw [hsm] at hstep
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
      obtain ⟨rfl, rfl⟩ := hstep
      obtain ⟨hbe, hnb⟩ := leaf_stepBound (hcheck_leaf hr hlc) hseed hsm
      exact ⟨hbe, applyNexts_bound hinv hnb⟩
  | m + 1 => by
    intro child f r hr hrn hlc cin env s cres s' hin hinv hstep
    obtain ⟨hst, hkids⟩ := hinv
    obtain ⟨hbF, hst', hkids'⟩ := moduleStepBoundH ms rk m (KSn_stepBoundH ms rk m) hr (by omega) hlc
      (connEnvS_bound hin hst) hst hkids hstep
    exact ⟨hbF, hst', hkids'⟩

/-- **Every cycle's environment of the run stays within the emitted widths, over `hcheck`.** -/
theorem runModuleTG_envBoundH (ms : List Module) (rk : String → Option Nat) (n : Nat) {o : Module} {f r : Nat}
    (hr : rk o.name = some r) (hrn : r ≤ n + 1)
    (hchk : hcheck (Tools.ShippingMachineLinked.childMap ms) rk f o = true)
    {seed : Nat → (String → Nat) → Env}
    (hseedB : ∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st)) :
    ∀ (T : Nat) (s : KState (KT n)) (envs : List Env),
      Bounded (weS o) s.st →
      (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
        Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
        InvN (Tools.ShippingMachineLinked.childMap ms) n gc (s.kids iname)) →
      runModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) n) (declWidth o)
        (Tools.ShippingMachineLinked.childMap ms) o.body seed T s = some envs →
      ∀ j (hj : j < envs.length), Bounded (weS o) (envs[j]'hj)
  | 0, s, envs, _, _, h, j, hj => by
    simp only [runModuleTG, Option.some.injEq] at h
    subst h; cases hj
  | k + 1, s, envs, hst, hkids, h, j, hj => by
    simp only [runModuleTG] at h
    cases hS : stepModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) n) (declWidth o)
        (Tools.ShippingMachineLinked.childMap ms) o.body (seed k s.st) s with
    | none => simp [hS] at h
    | some r' =>
    obtain ⟨envF, s'⟩ := r'
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) n) (declWidth o)
        (Tools.ShippingMachineLinked.childMap ms) o.body seed k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    obtain ⟨hbF, hst', hkids'⟩ := moduleStepBoundH ms rk n (KSn_stepBoundH ms rk n) hr hrn hchk (hseedB k s.st hst)
      hst hkids hS
    cases j with
    | zero => exact hbF
    | succ j => exact runModuleTG_envBoundH ms rk n hr hrn hchk hseedB k s' rest hst' hkids' hR j (by simpa using hj)

/-- **`SVBoundsH` from the height check** (`svBounds_of_checks` over `hcheck`): from `hcheck` at the module's own rank, a top seeding within the emitted widths, a bounded start state and
the instances' states within their emitted widths (`InvN`), the width premises of `design_sv_runH` hold along the run. -/
theorem svBoundsH_of_checks (ms : List Module) (rk : String → Option Nat) :
    ∀ (n : Nat) (o : Module) (seed : Nat → (String → Nat) → Env) (T : Nat) (s : KState (KT n))
      (envs : List Env) (f r : Nat),
      rk o.name = some r → r ≤ n + 1 →
      hcheck (Tools.ShippingMachineLinked.childMap ms) rk f o = true →
      (∀ k st, Bounded (weS o) st → Bounded (weS o) (seed k st)) →
      Bounded (weS o) s.st →
      (∀ mn iname conns gc gcwe, Stmt.inst mn iname conns ∈ o.body →
        Tools.ShippingMachineLinked.childMap ms mn = some (gc, gcwe) →
        InvN (Tools.ShippingMachineLinked.childMap ms) n gc (s.kids iname)) →
      runModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) n) (declWidth o)
        (Tools.ShippingMachineLinked.childMap ms) o.body seed T s = some envs →
      SVBoundsH (Tools.ShippingMachineLinked.childMap ms) rk n o seed T s envs := by
  intro n
  induction n with
  | zero =>
    intro o seed T s envs f r hr hrn hchk hseedB hst hkids hrun
    cases r with
    | zero =>
      unfold SVBoundsH; rw [if_pos hr]; exact ⟨hseedB, hst⟩
    | succ h' =>
      obtain ⟨f', rfl⟩ := hcheck_fuel hr hchk
      have hE := envAt_bound (T := T) (runModuleTG_envBoundH ms rk 0 hr hrn hchk hseedB T s envs hst hkids hrun)
      obtain ⟨htxt, hedge⟩ := (hcheck_succ_iff hr f').mp hchk
      obtain ⟨-, -, -, -, -, -, hpm, -⟩ := textCheckI_sound htxt
      unfold SVBoundsH; rw [if_neg (by rw [hr]; simp)]
      refine ⟨⟨oracle_bound hE hseedB, hst⟩, ?_⟩
      intro mn iname conns child cwe hm hc
      refine ⟨fun k st' hst' => connEnvS_bound (fun c hcin w hw => ?_) hst', hkids mn iname conns child cwe hm hc⟩
      have := hE k w
      rwa [hpm mn iname conns child cwe hm hc c (List.mem_filter.mp hcin).1 w hw] at this
  | succ m ih =>
    intro o seed T s envs f r hr hrn hchk hseedB hst hkids hrun
    cases r with
    | zero =>
      unfold SVBoundsH; rw [if_pos hr]; exact ⟨hseedB, hst⟩
    | succ h' =>
      obtain ⟨f', rfl⟩ := hcheck_fuel hr hchk
      have hE := envAt_bound (T := T) (runModuleTG_envBoundH ms rk (m + 1) hr hrn hchk hseedB T s envs hst hkids hrun)
      obtain ⟨htxt, hedge⟩ := (hcheck_succ_iff hr f').mp hchk
      obtain ⟨-, -, -, -, -, -, hpm, -⟩ := textCheckI_sound htxt
      unfold SVBoundsH; rw [if_neg (by rw [hr]; simp)]
      refine ⟨⟨oracle_bound hE hseedB, hst⟩, ?_⟩
      intro mn iname conns child cwe hm hc cenvs hcr
      obtain ⟨child', cwe', r', hc', hrk, hle, hname, hkc⟩ := hedge mn iname conns hm
      rw [hc] at hc'; cases hc'
      obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
      cases hxe
      obtain ⟨hcst, hgk⟩ := hkids mn iname conns child _ hm hc
      exact ih child _ T (s.kids iname) cenvs f' r' (by rw [hname]; exact hrk) (by omega) hkc
        (fun k st' hst' => connEnvS_bound (fun c hcin w hw => by
          have := hE k w
          rwa [hpm mn iname conns child _ hm hc c (List.mem_filter.mp hcin).1 w hw] at this) hst')
        hcst hgk hcr

/-! ## K2: the uniform bounds give the height-indexed bounds (under `hcheck` and the rank facts) -/

theorem bodyInstOuts_instFree (C : String → Option (Module × WEnv)) :
    ∀ (body : List Stmt), instFree body → bodyInstOuts C body = []
  | [], _ => rfl
  | st :: rest, h => by
    have h1 := h st List.mem_cons_self
    have h2 : instFree rest := fun x hx => h x (List.mem_cons_of_mem _ hx)
    cases st with
    | inst mn iname conns => simp [Sparkle.IR.Machine.isInst] at h1
    | _ => simp [bodyInstOuts, stmtInstOuts, bodyInstOuts_instFree C rest h2]

/-- an instance-free module's oracle seeding IS its seeding, so `ParentBounds` is `LeafBounds` -/
theorem leafBounds_of_parentBounds {C : String → Option (Module × WEnv)} {o : Module} (hf : instFree o.body)
    {seed : Nat → (String → Nat) → Env} {T : Nat} {st : String → Nat} {envs : List Env}
    (h : ParentBounds C o seed T st envs) : LeafBounds o seed st := by
  refine ⟨fun k st' hb => ?_, h.2⟩
  have := h.1 k st' hb
  have e : oracle C o.body (envAt envs T) seed k st' = seed k st' := by
    funext n; simp [oracle, seedOuts, bodyInstOuts_instFree C o.body hf]
  rwa [e] at this

/-- **Uniform `SVBounds` ⇒ `SVBoundsH`**, for a module of rank `r ≤ n + 1` passing `hcheck`.  The only difference of the two definitions is at rank 0 (a leaf: `LeafBounds` on the seeding itself
instead of `ParentBounds` on the oracle seeding); there `hcheck` gives `leafCheck`, hence an instance-free body, where the oracle is the seeding. -/
theorem svBoundsH_of_svBounds (C : String → Option (Module × WEnv)) (rk : String → Option Nat) :
    ∀ (n : Nat) (o : Module) (seed : Nat → (String → Nat) → Env) (T : Nat) (s : KState (KT n))
      (envs : List Env) (f r : Nat),
      rk o.name = some r → r ≤ n + 1 → hcheck C rk f o = true →
      SVBounds C n o seed T s envs → SVBoundsH C rk n o seed T s envs := by
  intro n
  induction n with
  | zero =>
    intro o seed T s envs f r hr hrn hchk hB
    cases r with
    | zero =>
      unfold SVBoundsH; rw [if_pos hr]
      exact leafBounds_of_parentBounds (instFree_of_leafCheck (hcheck_leaf hr hchk)) hB.1
    | succ h' =>
      unfold SVBoundsH; rw [if_neg (by rw [hr]; simp)]
      exact ⟨hB.1, fun mn iname conns child cwe hm hc => hB.2 mn iname conns child cwe hm hc⟩
  | succ m ih =>
    intro o seed T s envs f r hr hrn hchk hB
    cases r with
    | zero =>
      unfold SVBoundsH; rw [if_pos hr]
      exact leafBounds_of_parentBounds (instFree_of_leafCheck (hcheck_leaf hr hchk)) hB.1
    | succ h' =>
      obtain ⟨f', rfl⟩ := hcheck_fuel hr hchk
      obtain ⟨-, hedge⟩ := (hcheck_succ_iff hr f').mp hchk
      unfold SVBoundsH; rw [if_neg (by rw [hr]; simp)]
      refine ⟨hB.1, ?_⟩
      intro mn iname conns child cwe hm hc cenvs hcr
      obtain ⟨child', cwe', r', hc', hrk, hle, hname, hkc⟩ := hedge mn iname conns hm
      rw [hc] at hc'; cases hc'
      exact ih child _ T (s.kids iname) cenvs f' r' (by rw [hname]; exact hrk) (by omega) hkc
        (hB.2 mn iname conns child cwe hm hc cenvs hcr)

end Tools.ShippingSrm11Bounds
