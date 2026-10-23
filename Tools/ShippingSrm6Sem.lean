import Tools.ShippingSrm5Height
import Tools.ShippingDesignSVBounds
-- UNBUILT (unit SRM6): see STATUS-SRM6.md for run names.
-- SCOPE (binding): the SEMANTIC side of SRM5's `hcheck`.  `design_sv_runH` is the height-indexed restatement of `Tools.ShippingDesignSV.design_sv_runN` (the forward simulation of the IR linked
-- run by the emitted texts): its check hypothesis `designCheck C n o = true` is replaced by `hcheck C rk f o = true`, its relation `DesignSV C n` by `DesignSVH C rk n` and its width
-- premises `SVBounds C n` by `SVBoundsH C rk n` (the same premises, per kid at ITS rank).  A module of rank 0 is an instance-free leaf: its text runs as `LeafRun` at ANY state depth
-- (`runKS_instFree`), which is exactly what the uniform `DesignSV` cannot say for a built memory module below depth 0.
-- PREMISES kept (named): `hr`/`hrn` (the module's rank is `r` and `r ≤ n + 1`, `n` the depth of the stateful run), the IR run `hrun`, the width premises `SVBoundsH`.
-- NOT claimed: a rank supply, the machine-side premises of the endpoint (`InvN`/`Reset` at height-varying kids, `svBounds_of_checks`), `machine_design_svH_full`, K-ary assembly.
-- No `sorry`, no `axiom`, no `native_decide`, no heartbeat option.
namespace Tools.ShippingSrm6Sem
open Sparkle.IR.AST Sparkle.IR.Semantics Tools.ShippingDesignSV Tools.ShippingSrm5Height
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierSVRun (oracle)
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOptRun

/-- **The closed run of a design's emitted texts, height-indexed.**  The state is `KState (KT n)` (kids `KT n`): a module of rank 0 is a leaf (`LeafRun`);
any other module has the emitted text running (`TextRun`), its instances resolved, its connections width-matched, and each instance's child running
its own relation from the instance's state (at `n = 0` the kids have the flat state `KidState`: `LeafRun`). -/
def DesignSVH (C : String → Option (Module × WEnv)) (rk : String → Option Nat) :
    (n : Nat) → Module → (Nat → (String → Nat) → Env) → Nat → KState (KT n) → List Env → Prop
  | 0, o, seed, T, s, envs =>
    if rk o.name = some 0 then LeafRun o seed T s.st s.mems envs else
    TextRun o (oracle C o.body (envAt envs T) seed) T s.st s.mems envs ∧ Resolved C o.body ∧
    PortsMatch C o ∧
    ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
      ∃ cenvs, LeafRun child (connSeed (inConns child.outputs conns) (envAt envs T)) T
          (KidState.st (s.kids iname)) (KidState.mems (s.kids iname)) cenvs ∧
        Supplies child conns envs cenvs
  | n + 1, o, seed, T, s, envs =>
    if rk o.name = some 0 then LeafRun o seed T s.st s.mems envs else
    TextRun o (oracle C o.body (envAt envs T) seed) T s.st s.mems envs ∧ Resolved C o.body ∧
    PortsMatch C o ∧
    ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
      ∃ cenvs, DesignSVH C rk n child (connSeed (inConns child.outputs conns) (envAt envs T)) T
          (s.kids iname) cenvs ∧
        Supplies child conns envs cenvs

/-- The width premises of a leaf: its seeding and start registers within its emitted widths. -/
def LeafBounds (o : Module) (seed : Nat → (String → Nat) → Env) (st : String → Nat) : Prop :=
  (∀ k st', Bounded (weS o) st' → Bounded (weS o) (seed k st')) ∧ Bounded (weS o) st

/-- **The width premises along the IR run, height-indexed** (`SVBounds` with a rank-0 module a leaf). -/
def SVBoundsH (C : String → Option (Module × WEnv)) (rk : String → Option Nat) :
    (n : Nat) → Module → (Nat → (String → Nat) → Env) → Nat → KState (KT n) → List Env → Prop
  | 0, o, seed, T, s, envs =>
    if rk o.name = some 0 then LeafBounds o seed s.st else
    ParentBounds C o seed T s.st envs ∧
    ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
      LeafBounds child (connSeed (inConns child.outputs conns) (envAt envs T)) (KidState.st (s.kids iname))
  | n + 1, o, seed, T, s, envs =>
    if rk o.name = some 0 then LeafBounds o seed s.st else
    ParentBounds C o seed T s.st envs ∧
    ∀ mn iname conns child cwe, Stmt.inst mn iname conns ∈ o.body → C mn = some (child, cwe) →
      ∀ cenvs, runModuleTG (KSn C n) (declWidth child) C child.body
          (connSeed (inConns child.outputs conns) (envAt envs T)) T (s.kids iname) = some cenvs →
        SVBoundsH C rk n child (connSeed (inConns child.outputs conns) (envAt envs T)) T (s.kids iname) cenvs

variable {C : String → Option (Module × WEnv)} {rk : String → Option Nat}

/-- a rank-0 module that passes `hcheck` passes `leafCheck` (at every fuel) -/
theorem hcheck_leaf {o : Module} {f : Nat} (hr : rk o.name = some 0) (hc : hcheck C rk f o = true) :
    leafCheck o = true := by
  cases f <;> simp_all [hcheck]

/-- a module of positive rank that passes `hcheck` has a positive fuel -/
theorem hcheck_fuel {o : Module} {h f : Nat} (hr : rk o.name = some (h + 1)) (hc : hcheck C rk f o = true) :
    ∃ f', f = f' + 1 := by
  cases f with
  | zero => simp [hcheck, hr] at hc
  | succ f' => exact ⟨f', rfl⟩

/-- a module that passes `leafCheck` has no instance statement -/
theorem instFree_of_leafCheck {o : Module} (h : leafCheck o = true) : instFree o.body := by
  intro st hst
  have := List.all_eq_true.mp (leafCheck_parts h).1 st hst
  cases st <;> simp_all [seqStmtOkA, Sparkle.IR.Machine.isInst]

/-- **A rank-0 module's IR run at any depth is a closed text run** (`LeafRun`): it is instance-free, so it runs flat whatever the children's step. -/
theorem leaf_forwardH {o : Module} (hl : leafCheck o = true) {n : Nat} (ms : List Module)
    {seed : Nat → (String → Nat) → Env} {T : Nat} {s : KState (KT n)} {envs : List Env}
    (hrun : runModuleTG (KSn (Tools.ShippingMachineLinked.childMap ms) n) (declWidth o)
      (Tools.ShippingMachineLinked.childMap ms) o.body seed T s = some envs)
    (hb : LeafBounds o seed s.st) : LeafRun o seed T s.st s.mems envs := by
  rw [runModuleTG_instFree _ _ _ _ (instFree_of_leafCheck hl)] at hrun
  exact leaf_forward hl hb.1 hb.2 hrun

/-- **The IR linked run at depth `n` is a closed run of the design's emitted texts, over `hcheck`** (forward simulation; `design_sv_runN` restated).
`hr : rk o.name = some r`, `hrn : r ≤ n + 1`: the module's rank fits the depth of the stateful run (the kids are `KT n`). -/
theorem design_sv_runH (ms : List Module) :
    let C := Tools.ShippingMachineLinked.childMap ms
    ∀ (rk : String → Option Nat) (n : Nat) (o : Module) (seed : Nat → (String → Nat) → Env) (T : Nat) (s : KState (KT n))
      (envs : List Env) (f r : Nat),
      rk o.name = some r → r ≤ n + 1 →
      hcheck C rk f o = true →
      runModuleTG (KSn C n) (declWidth o) C o.body seed T s = some envs →
      SVBoundsH C rk n o seed T s envs →
      DesignSVH C rk n o seed T s envs := by
  intro C rk n
  induction n with
  | zero =>
    intro o seed T s envs f r hr hrn hchk hrun hB
    cases r with
    | zero =>
      unfold DesignSVH; unfold SVBoundsH at hB
      rw [if_pos hr] at hB ⊢
      exact leaf_forwardH (hcheck_leaf hr hchk) ms hrun hB
    | succ h =>
      obtain ⟨f', rfl⟩ := hcheck_fuel hr hchk
      have hh : h = 0 := by omega
      subst hh
      obtain ⟨htxt, hedge⟩ := (hcheck_succ_iff hr f').mp hchk
      unfold DesignSVH; unfold SVBoundsH at hB
      rw [if_neg (by rw [hr]; simp)] at hB ⊢
      obtain ⟨hok, hsv, hwg, hwf, hnd, hns, hpm, hres⟩ := textCheckI_sound htxt
      obtain ⟨⟨hsb, hst⟩, hkB⟩ := hB
      have hlen := runModuleTG_length (KSn C 0) _ C o.body seed T s envs hrun
      refine ⟨Tools.ShippingHierSVRun.linked_sv_run (KSn C 0) C hwf hok hsv hwg hrun hsb hst, hres, hpm, ?_⟩
      intro mn iname conns child cwe hm hc
      obtain ⟨child', cwe', r', hc', hrk, hle, hname, hkc⟩ := hedge mn iname conns hm
      rw [hc] at hc'; cases hc'
      have hr0 : r' = 0 := by omega
      subst hr0
      have hleaf : leafCheck child = true := hcheck_leaf (by rw [hname]; exact hrk) hkc
      obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
      cases hxe
      obtain ⟨cenvs, hcr, hsup⟩ := child_runKS_of_linked (KSn C 0) (KSn_local C 0) _ C o.body seed
        (envAt envs T) hwf hnd hm hc (Tools.ShippingHierPremisesBase.noSelfRead_sound hns mn iname conns hm child _ hc)
        T s envs hrun (envAt_spec hlen)
      have hcr' : runModule (declWidth child) child.body
          (connSeed (inConns child.outputs conns) (envAt envs T)) T
          (KidState.st (s.kids iname)) (KidState.mems (s.kids iname)) = some cenvs := by
        have := runKS_flat child (declWidth child) (inConns child.outputs conns) (envAt envs T) T (s.kids iname)
        exact this.symm.trans hcr
      obtain ⟨hcs, hcst⟩ := hkB mn iname conns child _ hm hc
      exact ⟨cenvs, leaf_forward hleaf hcs hcst hcr', hsup⟩
  | succ m ih =>
    intro o seed T s envs f r hr hrn hchk hrun hB
    cases r with
    | zero =>
      unfold DesignSVH; unfold SVBoundsH at hB
      rw [if_pos hr] at hB ⊢
      exact leaf_forwardH (hcheck_leaf hr hchk) ms hrun hB
    | succ h =>
      obtain ⟨f', rfl⟩ := hcheck_fuel hr hchk
      obtain ⟨htxt, hedge⟩ := (hcheck_succ_iff hr f').mp hchk
      unfold DesignSVH; unfold SVBoundsH at hB
      rw [if_neg (by rw [hr]; simp)] at hB ⊢
      obtain ⟨hok, hsv, hwg, hwf, hnd, hns, hpm, hres⟩ := textCheckI_sound htxt
      obtain ⟨⟨hsb, hst⟩, hkB⟩ := hB
      have hlen := runModuleTG_length (KSn C (m + 1)) _ C o.body seed T s envs hrun
      refine ⟨Tools.ShippingHierSVRun.linked_sv_run (KSn C (m + 1)) C hwf hok hsv hwg hrun hsb hst, hres, hpm, ?_⟩
      intro mn iname conns child cwe hm hc
      obtain ⟨child', cwe', r', hc', hrk, hle, hname, hkc⟩ := hedge mn iname conns hm
      rw [hc] at hc'; cases hc'
      obtain ⟨x, -, hxe⟩ := Tools.ShippingHierPremisesBase.childMap_some' hc
      cases hxe
      obtain ⟨cenvs, hcr, hsup⟩ := child_runKS_of_linked (KSn C (m + 1)) (KSn_local C (m + 1)) _ C
        o.body seed (envAt envs T) hwf hnd hm hc
        (Tools.ShippingHierPremisesBase.noSelfRead_sound hns mn iname conns hm child _ hc)
        T s envs hrun (envAt_spec hlen)
      have hcr' : runModuleTG (KSn C m) (declWidth child) C child.body
          (connSeed (inConns child.outputs conns) (envAt envs T)) T (s.kids iname) = some cenvs := by
        have := runKS_succ (KSn C m) C child (declWidth child) (inConns child.outputs conns)
          (envAt envs T) T (s.kids iname)
        exact this.symm.trans hcr
      exact ⟨cenvs, ih child _ T (s.kids iname) cenvs f' r' (by rw [hname]; exact hrk) (by omega) hkc hcr'
        (hkB mn iname conns child _ hm hc cenvs hcr'), hsup⟩

end Tools.ShippingSrm6Sem
