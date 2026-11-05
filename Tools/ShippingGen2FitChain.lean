import Tools.ShippingGen2Fit
import Tools.ShippingGen2OneOut     -- ExtB, machine_linked_callsServed1, oneP/oneF, CallDec, OneOutCall
import Tools.ShippingSrm33Core      -- consumer 1, ComposedNWRegs (Srm28Regs), RunFacts
set_option autoImplicit false

/-! # S4-BD chain: the run-local fit along the one-output route (scripts/gen2/S4_FIT_FREEZE.md rev2, approved at
bbca065d, §2-§4)

BUILT: g2fc-c6951eb8 at c6951eb8 (exit 0; standard axioms).

Every type below is the frozen text of the freeze. The file has four blocks:
* Block 0 (`namespace Tools.ShippingGen2Fit`, the ambient of Tools/ShippingGen2Fit.lean, freeze §1.6):
  `ksBoundedRun_of_In` (freeze §4.1; placed here, not in Tools/ShippingGen2Fit.lean, because existing files are not
  edited; its fully qualified name is the frozen one).
* Block A (`namespace Tools.ShippingGen2Fit`, freeze §2 Block A ambient, verbatim): `CallValues`, `CallOutWidths`,
  `machine_linked_ofBV` (+ projection `machine_linked_ofB_viaV`), `ComposedHBF` (+ `toHB`), `ComposedNWF` (+ `toNW`),
  `composedNWn_of_HBF`, `ComposedNWRegsF` (+ `toRegs`), `composedNWRegsF_of_composedNWF`, `oneOut_lookup_callWire`,
  `oneOut_ksBoundedRun`, `binders_drop_at`, `composedNWRegsF_of_In`. The copied proofs name their helper lemmas fully
  qualified, so no open beyond the frozen ambient is added.
* Block B (`namespace Tools.ShippingGen2`, Tools/ShippingGen2OneOut.lean:31-55 at 99f0de5d verbatim): `OneOutWidth`
  (S4_CONSUMER_FREEZE.md §5 text), `machine_linked_callsServed1F` and the projection `example`.
* Block C (`namespace Tools.ShippingSrm33`, Tools/ShippingSrm33Core.lean:7-21 at f51e68a4 verbatim):
  `machine_ships_hierC_run`.

Same witness along the chain (freeze §3.6): `ids`/`cache`/`regs`/`lets`/`wired` are `h`'s, destructured once in
`machine_linked_callsServed1F` and re-packed unchanged by every lifting lemma; `envs` is the one `machine_linked_ofBV`
returns (the `trace … seed'` run), on which both `CallValues` and the fit are stated; `runModuleTG_KSn_of_H` returns the
same list; the seed and the time index are the tail's.
No sorry / axiom / native_decide. -/

/-! ## Block 0: `ksBoundedRun_of_In` (ambient of Tools/ShippingGen2Fit.lean) -/
namespace Tools.ShippingGen2Fit
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.HierCheck
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierStateG
open Tools.ShippingHierState Tools.ShippingHierOptLinked
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingHierOptRun

/-- **`KSBoundedIn` gives the run-local fit on a real run** (freeze §4.1), from linked well-formedness, distinct
instance names and the invariant on the initial children's states. The step decomposition is `fitX_of_run`'s
(Tools/ShippingHierOptRun.lean:690-716) with the memory step kept as a case (no `memFree`). -/
theorem ksBoundedRun_of_In {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    (W : WEnv) (body : List Stmt) (seed : Nat → (String → Nat) → Env) (Inv : Module → σ → Prop)
    (hKSb : KSBoundedIn children KS body Inv)
    (hwf : linkedWF children body = true) (hnd : (instNames body).Nodup) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS W children body seed T s = some envs →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
        children mn = some (child, cwe) → Inv child (s.kids iname)) →
      KSBoundedRun children body envs
  | 0, _, envs, h, _ => by
    simp only [runModuleTG, Option.some.injEq] at h
    subst h
    intro j hj
    exact absurd hj (by simp)
  | k + 1, s, envs, h, hinv => by
    simp only [runModuleTG] at h
    cases hS : stepModuleTG KS W children body (seed k s.st) s with
    | none => simp [hS] at h
    | some r =>
    obtain ⟨envF, s'⟩ := r
    simp only [hS, Option.bind_eq_bind, Option.bind_some] at h
    cases hR : runModuleTG KS W children body seed k s' with
    | none => simp [hR] at h
    | some rest =>
    simp only [hR, Option.bind_some, Option.some.injEq] at h
    subst h
    unfold stepModuleTG at hS
    cases hK : evalAssignsKG KS W children s.kids s.mems body (seed k s.st) s.kids with
    | none => simp [hK] at hS
    | some ek =>
    obtain ⟨envF', kids'⟩ := ek
    cases hN : regNexts W s.mems body envF' with
    | none => simp [hK, hN] at hS
    | some nexts =>
    cases hM : memNexts W body s.mems envF' with
    | none => simp [hK, hN, hM] at hS
    | some mems' =>
    simp only [hK, hN, hM, Option.bind_eq_bind, Option.bind_some,
      Option.some.injEq, Prod.mk.injEq] at hS
    obtain ⟨rfl, rfl⟩ := hS
    have hcons := Tools.ShippingHierOptLinked.linked_consistentKG KS W children s.kids s.mems body _ envF'
      s.kids kids' hwf hnd hK
    have hrest := ksBoundedRun_of_In KS children W body seed Inv hKSb hwf hnd k
      ⟨applyNexts s.st nexts, mems', kids'⟩ rest hR
      (fun mn iname conns hmem child cwe hc => by
        obtain ⟨child', cwe', envAt, cres, hc', hk, -, -⟩ := hcons mn iname conns hmem
        rw [hc] at hc'
        cases hc'
        exact (hKSb mn iname conns hmem child cwe hc _ _ _ _ (hinv _ _ _ hmem _ _ hc) hk).2)
    intro j hj mn iname conns hmem child cwe hc p hp x hl
    cases j with
    | zero =>
      show envF' x < _
      obtain ⟨child', cwe', envAt, cres, hc', hk, -, hout⟩ := hcons mn iname conns hmem
      rw [hc] at hc'
      cases hc'
      rw [hout p hp x hl]
      exact (hKSb mn iname conns hmem child cwe hc _ _ _ _ (hinv _ _ _ hmem _ _ hc) hk).1 p hp
    | succ j =>
      have h1 := hrest j (by simpa using hj) mn iname conns hmem child cwe hc p hp x hl
      simpa using h1

end Tools.ShippingGen2Fit

/-! ## Block A: the generic chain (freeze §2 Block A ambient) -/
namespace Tools.ShippingGen2Fit
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
-- AMBIENT FIX (freeze Block A lists `MachineShape` here): `Sparkle.IR.Machine.MachineShape` does not exist
-- (`MachineShape` is `Sparkle.Compiler.Elab.MachineShape`, Sparkle/Compiler/Elab.lean:5028) and `open Ns (x)` fails on an
-- unknown `Ns.x`. Dropped; `MachineShape` resolves through `open Sparkle.Compiler.Elab` above, so no type changes.
open Sparkle.IR.Machine (OutField SlotField moduleByName)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness (weOf)
open Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked (childMap runModuleH)
open Tools.ShippingMachineDepth
open Tools.ShippingMachineShipsDepth (ResetNk)

/-! ### §3.1 Two predicates -/

/-- c3: on the run `envs`, call `k`'s wire carries the encoded call-result binder at the same cycle `j`. -/
def CallValues (declName : Name) (d : MachineData) (kD : Nat) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) {ι : Type} {dom : ι → DomainConfig}
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (envs : List Env) : Prop :=
  ∀ j (hj : j < envs.length) (k : Nat) (outW : String), k < d.shape.insts.length →
    ((machPorts declName ids cache d.shape.binders).map (·.name))[machNIn d.shape + k]? = some outW →
    (envs[j]'hj) outW =
      posEnc (fun p => (extB i bools bits p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
        (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)

/-- d2 on one witness: every call `k`'s module's output port has the width of call `k`'s result binder. -/
def CallOutWidths (declName : Name) (d : MachineData) (kD : Nat) (ids : List FVarId)
    (cache : IO.Ref (ExprStructMap String)) (m : Sparkle.IR.AST.Module) (dsn : Design) : Prop :=
  ∀ (k : Nat) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
    (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
    Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length d.shape.layout.slots.length
      ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
    moduleByName dsn.modules mc.name = some mc →
    ∀ outP ∈ mc.outputs,
      outP.ty.bitWidth = (kindTy (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)).bitWidth

/-! ### §3.2 `machine_linked_ofBV` (c3) and its projection -/

/-- `machine_linked_ofB` (Tools/ShippingMachineExtB.lean:100-363, 4c2953c3) with the conclusion extended by
`CallValues` on the SAME `envs`: the wire value the accepted proof already computes (`hframe` + `hon`) is exposed.
Proof: the accepted proof verbatim (helper lemmas fully qualified), the final `refine` with one more `?_`. -/
theorem machine_linked_ofBV {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module} {dsn : Design}
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
      (∀ k args mc st, (d.shape.insts.map (·.2.1))[k]? = some args → st ∈ m.body →
        Tools.ShippingMachineInst.CallStmt (machNIn d.shape) d.shape.insts.length
          d.shape.layout.slots.length
          ((machPorts declName ids cache d.shape.binders).map (·.name)) k args mc st →
        Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc →
        Tools.ShippingMachineCompose.ChildFn mc (P k) (F k)) →
      (∀ k args j, (d.shape.insts.map (·.2.1))[k]? = some args → j < T →
        (∀ q ∈ args, q < d.ls.length ∧ q < (lsrc i bools bits).length) ∧
        P k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) ∧
        F k (args.map fun q => ((lsrc i bools bits)[q]?.map (· j)).getD 0) =
          posEnc (fun p => (extB i bools bits p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)
            (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)) →
      ∃ envs, runModuleH (weOf m) (childMap dsn.modules) m.body seed T st0 mems = some envs ∧
        envs.length = T ∧
        (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j) ∧
        CallValues declName d kD ids cache ext extB i bools bits envs := by
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
  obtain ⟨restP, hrestP⟩ := Tools.ShippingMachineCompose.machPorts_append (declName := declName) (cache := cache)
    (bsD ++ bsI) (d.slotBs ++ d.letBs) hlenB
  have hlenDI : bsD.length + bsI.length ≤ ids.length := by
    have := hlenB; simp only [List.length_append] at this ⊢; omega
  obtain ⟨insP, hinsP⟩ := Tools.ShippingMachineCompose.machPorts_append (declName := declName) (cache := cache)
    bsD bsI hlenDI
  have hDlen : (machPorts declName ids cache bsD).length = machNIn d.shape := by
    rw [hNIn]; exact Tools.ShippingMachineCompose.machPorts_length bsD (by omega)
  have hDIlen : (machPorts declName ids cache (bsD ++ bsI)).length =
      machNIn d.shape + d.shape.insts.length := by
    rw [Tools.ShippingMachineCompose.machPorts_length _ (by omega), List.filter_append, List.length_append, ← hNIn,
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
      rw [List.length_append,
        Tools.ShippingMachineCompose.machPorts_length _ (by simp only [List.length_append] at hlenB ⊢; omega),
        Tools.ShippingMachineCompose.machPorts_length _ (by omega : (bsD ++ bsI).length ≤ ids.length),
        List.filter_append,
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
      rw [← this]; exact Tools.ShippingMachineCompose.idxOf_nodup hinsNd k _
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
      have hsrc := Tools.ShippingMachineCompose.sourceInputs_extend (declName := declName) nd hlenDI hI hnd'
        (hin t st ht)
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
    rw [← Tools.ShippingMachineLinked.linkedOk_eq]; exact link
  have hoff' : ∀ t st n, n ∉ bodyInstOuts (childMap dsn.modules) m.body →
      seed' t st n = seed t st n := by
    intro t st n hn
    apply hoff
    intro hni
    obtain ⟨k, hk, hkn⟩ := List.getElem_of_mem hni
    have hk' : k < d.shape.insts.length := by simp [insNames, hinsLen] at hk; exact hk
    obtain ⟨args, mc, st', _, hst', hmc, hcall⟩ := calls k hk'
    exact hn (Tools.ShippingMachineCompose.callStmt_out hst' hcall hmc
      (by rw [hinsAt k hk', List.getElem?_eq_getElem hk, hkn]))
  obtain ⟨_, henvs⟩ := Tools.ShippingMachineCompose.runModule_envs (weOf m) m.body seed' T st0 mems envs hrun
  refine ⟨envs, Tools.ShippingMachineCompose.runModuleH_of_run (weOf m) (childMap dsn.modules) m.body seed seed'
    hwf hoff' T st0 mems envs hrun ?_, hlenE, hobs, ?_⟩
  · -- the children compute the calls' values (ExtB.lean:309-363, verbatim)
    intro j hj mems' mn iname conns hmem
    obtain ⟨k, args, mc, hargs, hmc, hcall⟩ := insts mn iname conns hmem
    have hname : mc.name = mn := Tools.ShippingMachineInst.moduleByName_name hmc
    have hmc' : Sparkle.IR.Machine.moduleByName dsn.modules mc.name = some mc := by
      rw [hname]; exact hmc
    have hjT : j < T := by omega
    obtain ⟨hq, hP, hF⟩ := hval k args j hargs hjT
    refine Tools.ShippingMachineCompose.childComputes_of_call hmc hcall (hchild k args mc _ hargs hmem hcall hmc') ?_
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
    have hframe := Tools.ShippingMachineLinked.evalAssigns_frame (weOf m) memsj (childMap dsn.modules) m.body _ _
      outW hwf hev
      (Tools.ShippingMachineCompose.instOuts_not_written m.body outW hwf (by
        rw [hout']
        obtain ⟨args', mc', st', _, hst', hmc'', hcall'⟩ := calls k hkI
        exact Tools.ShippingMachineCompose.callStmt_out hst' hcall' hmc'' (by
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
  · -- c3 (`CallValues`): the same frame + seed argument, on the same `envs`, for every call `k`
    intro j hj k outW hk hx
    have hx' : names[machNIn d.shape + k]? = some outW := hx
    have hxo : outW = insNames[k]'(by simp [insNames, hinsLen]; exact hk) := by
      rw [hinsAt k hk, List.getElem?_eq_getElem (by simp [insNames, hinsLen]; exact hk)] at hx'
      exact (Option.some.inj hx').symm
    obtain ⟨stj, memsj, hev⟩ := henvs j hj
    have hframe := Tools.ShippingMachineLinked.evalAssigns_frame (weOf m) memsj (childMap dsn.modules) m.body _ _
      outW hwf hev
      (Tools.ShippingMachineCompose.instOuts_not_written m.body outW hwf (by
        rw [hxo]
        obtain ⟨args', mc', st', _, hst', hmc'', hcall'⟩ := calls k hk
        exact Tools.ShippingMachineCompose.callStmt_out hst' hcall' hmc'' (by
          rw [hinsAt k hk, List.getElem?_eq_getElem (by simp [insNames, hinsLen]; exact hk)])))
    have hpk : insP[k]? = some (insP[k]'(by rw [hinsLen]; exact hk)) :=
      List.getElem?_eq_getElem _
    have hseedv := hon (T - 1 - j) stj k _ hpk
    rw [hframe, hxo]
    simp only [insNames, List.getElem_map]
    rw [hseedv]
    have : T - 1 - (T - 1 - j) = j := by omega
    rw [this]

/-- PROJECTION: the statement is `machine_linked_ofB`'s (Tools/ShippingMachineExtB.lean:100-171, 4c2953c3) verbatim,
renamed (`ChildFn` written fully qualified: the same constant). Dropping the value conjunct gives the accepted type. -/
theorem machine_linked_ofB_viaV {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module} {dsn : Design}
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
        Tools.ShippingMachineCompose.ChildFn mc (P k) (F k)) →
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
  intro i bools bits T seed st0 mems hsrc hpass hrst hinit hchild hval
  obtain ⟨envs, h1, h2, h3, -⟩ := machine_linked_ofBV nd len rnd rlen llen wired trace hsimple kD hkD hI hIlen hSL
    hSlen hLlen hNIn P F i bools bits T seed st0 mems hsrc hpass hrst hinit hchild hval
  exact ⟨envs, h1, h2, h3⟩

/-! ### §3.3 `ComposedHBF`, `ComposedNWF`, `composedNWn_of_HBF` and their projections -/

/-- `ComposedHB` (ExtB.lean:36-70, 4c2953c3) with ONE extra conjunct of the run tail, on the same `envs`: the run-local fit. -/
def ComposedHBF (R : Nat → Sparkle.IR.AST.Module → Prop) (declName : Name) (d : MachineData) (kD : Nat)
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
        (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j) ∧
        KSBoundedRun (childMap dsn.modules) m.body envs

/-- PROJECTION: forgetting the fit gives stage A's `ComposedHB` (same witness, same `envs`). -/
theorem ComposedHBF.toHB {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (h : ComposedHBF R declName d kD m dsn dom src ext extB) :
    Tools.ShippingMachineShipsHierH.ComposedHB R declName d kD m dsn dom src ext extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems hsrc hpass hrst hinit hR
  obtain ⟨envs, hrun, hlen, hobs, -⟩ := H i bools bits T seed st0 mems hsrc hpass hrst hinit hR
  exact ⟨envs, hrun, hlen, hobs⟩

/-- `ComposedNW` (Tools/ShippingMachineDepthRun.lean:34-62, 2af72c05) with the same extra conjunct. -/
def ComposedNWF (n : Nat) (declName : Name) (d : MachineData) (kD : Nat) (m : Sparkle.IR.AST.Module) (dsn : Design)
    {ι : Type} (dom : ι → DomainConfig)
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
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
      (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t))
        (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      (∀ (iname : String) (mc : Sparkle.IR.AST.Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
        moduleByName dsn.modules mc.name = some mc → ResetN dsn n mc (kids iname)) →
      ∃ envs, runModuleTG (KSn (childMap dsn.modules) n) (weOf m)
          (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ = some envs ∧
        envs.length = T ∧
        (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j) ∧
        KSBoundedRun (childMap dsn.modules) m.body envs

/-- `composedNWn_of_HB` (ExtB.lean:455-479, 4c2953c3) with `ComposedHBF` / `ComposedNWF`; same premises `hB`, `hcomb`.
`runModuleTG_KSn_of_H` returns `some envs` for the SAME `envs`, so the fit passes through unchanged. -/
theorem composedNWn_of_HBF (n : Nat) {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (hC : ComposedHBF R declName d kD m dsn dom src ext extB)
    (hB : Tools.ShippingMachineDepthH.BoundH R declName d m dsn)
    (hcomb : Tools.ShippingMachineDepthH.kidsComb dsn.modules m.body = true) :
    ComposedNWF n declName d kD m dsn dom src ext extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩ := hC
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  -- the body's linked well-formedness: its wiring
  have hwf : linkedWF (childMap dsn.modules) m.body = true := by
    obtain ⟨_, _, _, _, _, _, hlink, _⟩ := wired
    rw [← Tools.ShippingMachineLinked.linkedOk_eq]; exact hlink
  intro i bools bits T seed st0 mems kids hsrc hpass hrst _ hinit _
  obtain ⟨envs, hrun, hlen, hobs, hfit⟩ := H i bools bits T seed st0 mems hsrc hpass hrst hinit
    (hB ids cache regs lets wired)
  refine ⟨envs, ?_, hlen, hobs, hfit⟩
  exact Tools.ShippingMachineDepthHR.runModuleTG_KSn_of_H n _ dsn.modules m.body seed
    (Tools.ShippingHierOptRun.memFree_of_linkedWF _ hwf) hcomb T st0 mems kids envs hrun

/-- PROJECTION: forgetting the fit gives `ComposedNW`, i.e. `composedNWn_of_HB`'s conclusion type (ExtB:466-467). -/
theorem ComposedNWF.toNW {n : Nat} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (h : ComposedNWF n declName d kD m dsn dom src ext extB) :
    Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems kids hsrc hpass hrst hclk hinit hreset
  obtain ⟨envs, hrun, hlen, hobs, -⟩ := H i bools bits T seed st0 mems kids hsrc hpass hrst hclk hinit hreset
  exact ⟨envs, hrun, hlen, hobs⟩

/-! ### §3.4 `ComposedNWRegsF` and its projection -/

/-- `ComposedNWRegs` (Tools/ShippingSrm28Regs.lean:41-75, 907659aa) with the same extra conjunct. -/
def ComposedNWRegsF (n : Nat) (declName : Name) (d : MachineData) (kD : Nat) (m : Sparkle.IR.AST.Module) (dsn : Design)
    {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool)
    (P : List String → Prop) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = d.ss.length ∧ P regs ∧
    ∃ lets : List String, lets.length = d.letBs.length ∧
    MachineWired declName d.shape ids cache m dsn regs lets ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
      (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (seed : Nat → (String → Nat) → Env) (st0 : String → Nat) (mems : MEnv)
      (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
        (fun j => (extB i bools bits j).val (T - 1 - t))
        (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seed t st)) →
      (∀ t st r, r ∈ regs → seed t st r = st r) →
      (∀ t st, seed t st "rst" = 0) → (∀ t st, seed t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      (∀ (iname : String) (mc : Sparkle.IR.AST.Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
        moduleByName dsn.modules mc.name = some mc → ResetN dsn n mc (kids iname)) →
      ∃ envs, runModuleTG (KSn (childMap dsn.modules) n) (weOf m)
          (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ = some envs ∧
        envs.length = T ∧
        (∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j) ∧
        KSBoundedRun (childMap dsn.modules) m.body envs

/-- As `composedNWRegs_of_composedNW` (Srm28Regs:77-94): the witness of `h`, `P` from the wiring. -/
theorem composedNWRegsF_of_composedNWF {n : Nat} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (P : List String → Prop)
    (h : ComposedNWF n declName d kD m dsn dom src ext extB)
    (hP : ∀ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs lets : List String),
      regs.Nodup → regs.length = d.ss.length →
      MachineWired declName d.shape ids cache m dsn regs lets → P regs) :
    ComposedNWRegsF n declName d kD m dsn dom src ext extB P := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩ := h
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, hP ids cache regs lets rnd rlen wired,
    lets, llen, wired, H⟩

/-- PROJECTION: forgetting the fit gives `ComposedNWRegs` (same witness, same `envs`). -/
theorem ComposedNWRegsF.toRegs {n : Nat} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {P : List String → Prop}
    (h : ComposedNWRegsF n declName d kD m dsn dom src ext extB P) :
    Tools.ShippingSrm28.ComposedNWRegs n declName d kD m dsn dom src ext extB P := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, hPr, lets, llen, wired, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, hPr, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems kids hsrc hpass hrst hclk hinit hreset
  obtain ⟨envs, hrun, hlen, hobs, -⟩ := H i bools bits T seed st0 mems kids hsrc hpass hrst hclk hinit hreset
  exact ⟨envs, hrun, hlen, hobs⟩

/-! ### §3.5 d1, e and the index lemma -/

/-- d1: a wire an instance's output drives is call `k`'s port `names[machNIn + k]`, and the child is call `k`'s module. -/
theorem oneOut_lookup_callWire {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Sparkle.IR.AST.Module} {dsn : Design} {regs lets : List String}
    (wired : MachineWired declName shape ids cache m dsn regs lets) (hsimple : shape.instFields = [])
    {mn iname : String} {conns : List (String × Sparkle.IR.AST.Expr)} (hmem : Stmt.inst mn iname conns ∈ m.body)
    {child : Sparkle.IR.AST.Module} {cwe : WEnv} (hc : childMap dsn.modules mn = some (child, cwe))
    {p : Port} (hp : p ∈ child.outputs) {x : String} (hl : conns.lookup p.name = some (.ref x)) :
    ∃ (k : Nat) (args : List Nat), (shape.insts.map (·.2.1))[k]? = some args ∧ k < shape.insts.length ∧
      moduleByName dsn.modules child.name = some child ∧
      Tools.ShippingMachineInst.CallStmt (machNIn shape) shape.insts.length shape.layout.slots.length
        ((machPorts declName ids cache shape.binders).map (·.name)) k args child (.inst mn iname conns) ∧
      child.outputs = [p] ∧
      ((machPorts declName ids cache shape.binders).map (·.name))[machNIn shape + k]? = some x := by
  -- `wired`'s 6th conjunct (Entry:667-669): the instance is call `k`'s `CallStmt`
  obtain ⟨_, _, _, _, _, insts, _⟩ := wired
  obtain ⟨k, args, mc, hargs, hmn, hcall⟩ := insts hsimple mn iname conns hmem
  -- the child the map serves is call `k`'s module
  obtain ⟨cx, hcx, hr⟩ := Tools.ShippingMachineDepthRun.childMap_some.mp hc
  have hcm : cx = mc := Option.some.inj (hcx.symm.trans hmn)
  have hch : child = mc := (Prod.mk.inj hr).1.trans hcm
  subst hch
  have hname : child.name = mn := Tools.ShippingMachineInst.moduleByName_name hmn
  have hmod : moduleByName dsn.modules child.name = some child := by rw [hname]; exact hmn
  have hk : k < shape.insts.length := by
    have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
  -- the `CallStmt` fields (Inst:190-203)
  obtain ⟨outW, argWs, outP, iname', hout, _, hpo, _, _, _, _, hnot, _, hst⟩ := id hcall
  injection hst with hmnEq hinEq hconns
  rw [hpo] at hp
  have hpe : p = outP := List.mem_singleton.mp hp
  subst hpe
  have hA : (child.inputs.filter fun q => q.name != "clk" && q.name != "rst") =
      Tools.ShippingMachineCompose.argPorts child := rfl
  rw [hA] at hnot hconns
  -- the output port's connection is the call's port wire
  have hlo : conns.lookup p.name = some (.ref outW) := by
    rw [hconns]
    have h1 := Tools.ShippingMachineCompose.lookup_zip_rest [(p.name, Sparkle.IR.AST.Expr.ref outW)] p.name
      (Tools.ShippingMachineCompose.argPorts child) argWs hnot
    rw [List.lookup_cons_self] at h1
    exact h1
  have hxw : x = outW := by
    have h2 := hl.symm.trans hlo
    simp only [Option.some.injEq, Sparkle.IR.AST.Expr.ref.injEq] at h2
    exact h2
  subst hxw
  exact ⟨k, args, hargs, hk, hmod, hcall, hpo, hout⟩

/-- e (generic): values on call wires + widths of call modules ⇒ the run-local fit. -/
theorem oneOut_ksBoundedRun {declName : Name} {d : MachineData} {kD : Nat} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Sparkle.IR.AST.Module} {dsn : Design}
    {regs lets : List String} {ι : Type} {dom : ι → DomainConfig}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {i : ι} {bools : Nat → Signal (dom i) Bool} {bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {envs : List Env}
    (wired : MachineWired declName d.shape ids cache m dsn regs lets)
    (hsimple : d.shape.instFields = [])
    (hW : CallOutWidths declName d kD ids cache m dsn)
    (hV : CallValues declName d kD ids cache ext extB i bools bits envs) :
    KSBoundedRun (childMap dsn.modules) m.body envs := by
  intro j hj mn iname conns hmem child cwe hc p hp x hl
  obtain ⟨k, args, hargs, hk, hmod, hcall, -, hx⟩ :=
    oneOut_lookup_callWire (declName := declName) (shape := d.shape) (ids := ids) (cache := cache) (m := m)
      (dsn := dsn) (regs := regs) (lets := lets) wired hsimple hmem hc hp hl
  rw [hV j hj k x hk hx, hW k args child (.inst mn iname conns) hargs hmem hcall hmod p hp]
  exact posEnc_lt _ _ _ _

/-- Index lemma (d2): call `k`'s result binder in `binders` is `(bsIn.drop kD)[k]`. -/
theorem binders_drop_at (d : MachineData) (kD k : Nat) (hk : k < (d.bsIn.drop kD).length) :
    d.shape.binders[kD + k]? = (d.bsIn.drop kD)[k]? := by
  have hlt : kD + k < d.nIn := by
    simp only [List.length_drop, Tools.ShippingMachineAuto.MachineData.bsIn, List.length_take] at hk
    omega
  rw [List.getElem?_drop]
  simp only [Tools.ShippingMachineAuto.MachineData.bsIn]
  rw [List.getElem?_take_of_lt hlt]

/-! ### §4.2 `composedNWRegsF_of_In` (the `KSBoundedIn` side) -/

/-- A `ComposedNWRegs` together with `KSBoundedIn` of its body, the reset-implies-invariant law and distinct instance
names is a `ComposedNWRegsF`: the witness of `h`, the fit from `ksBoundedRun_of_In` on the run `h` returns. -/
theorem composedNWRegsF_of_In {n : Nat} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {P : List String → Prop} (Inv : Sparkle.IR.AST.Module → KT n → Prop)
    (h : Tools.ShippingSrm28.ComposedNWRegs n declName d kD m dsn dom src ext extB P)
    (hKSb : Tools.ShippingHierOptRun.KSBoundedIn (childMap dsn.modules) (KSn (childMap dsn.modules) n) m.body Inv)
    (hRI : Tools.ShippingMachineShipsHier.ResetImpliesInv (ResetNk n) Inv)
    (hnd : (Tools.ShippingHierState.instNames m.body).Nodup) :
    ComposedNWRegsF n declName d kD m dsn dom src ext extB P := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, hPr, lets, llen, wired, H⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, hPr, lets, llen, wired, ?_⟩
  -- the body's linked well-formedness: its wiring (as ExtB:471-473)
  have hwf : linkedWF (childMap dsn.modules) m.body = true := by
    obtain ⟨_, _, _, _, _, _, hlink, _⟩ := wired
    rw [← Tools.ShippingMachineLinked.linkedOk_eq]; exact hlink
  intro i bools bits T seed st0 mems kids hsrc hpass hrst hclk hinit hreset
  obtain ⟨envs, hrun, hlen, hobs⟩ := H i bools bits T seed st0 mems kids hsrc hpass hrst hclk hinit hreset
  exact ⟨envs, hrun, hlen, hobs,
    ksBoundedRun_of_In (KSn (childMap dsn.modules) n) (childMap dsn.modules) (weOf m) m.body seed Inv hKSb hwf hnd
      T ⟨st0, mems, kids⟩ envs hrun (hRI m dsn kids hreset)⟩

end Tools.ShippingGen2Fit

/-! ## Block B: package level (Tools/ShippingGen2OneOut.lean:31-55 at 99f0de5d, verbatim) -/
namespace Tools.ShippingGen2
open Lean Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
open Tools.ShippingChildBndCore (cv dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- The binder of call `k`'s result has the bit width of the callee package's ONLY layout output (the unique output, not a field
name). `kindTy`: Tools/ShippingMachineEntry.lean:232. (S4_CONSUMER_FREEZE.md §5, approved rev2, unchanged.) -/
def OneOutWidth (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length) (q : Pkg ι dom), P (p.d.shape.insts[k]).1 = some q →
    ∀ o : OutField, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth

/-- `machine_linked_callsServed1` (OneOut:158-256, 99f0de5d) with premise `hW` added and conclusion `ComposedHBF`.
The proof is the accepted one with `machine_linked_ofB` replaced by `machine_linked_ofBV` (same arguments; the two call
premises discharged by the same tactic blocks, now as `by` arguments); the fit is `oneOut_ksBoundedRun` on the ONE
witness `h` (`wired`, `ids`, `cache`) and the ONE run `envs` `machine_linked_ofBV` returns, with `CallOutWidths` built
at the intro's `i` from `hW`, `hserve` (the served child's `CombChildRunN`, first conjunct) and `binders_drop_at`. -/
theorem machine_linked_callsServed1F (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hsimple : p.d.shape.instFields = [])
    (hkD : p.kD ≤ p.d.bsIn.length)
    (hI : ∀ b ∈ p.d.bsIn.drop p.kD, b.2 ≠ .domain)
    (hIlen : (p.d.bsIn.drop p.kD).length = p.d.shape.insts.length)
    (hSL : ∀ b ∈ p.d.slotBs ++ p.d.letBs, b.2 ≠ .domain)
    (hSlen : p.d.slotBs.length = p.d.shape.layout.slots.length)
    (hLlen : p.d.letBs.length = p.d.shape.layout.lets)
    (hNIn : machNIn p.d.shape = ((p.d.bsIn.take p.kD).filter (fun b => b.2 != .domain)).length)
    (hkc : kidsCombB D.modules raw.body = true)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length),
      ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (hW : ∀ k, OneOutWidth P p k) :
    Tools.ShippingGen2Fit.ComposedHBF (fun _ _ => True) p.decl p.d p.kD raw D dom p.src p.extS p.extBS := by
  -- AUDIT 1: ONE witness
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := h
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems hsrc hpass hrst hinit _
  -- the instance served to call `k` is a combinational run of the callee's package, assignments only
  have hserve : ∀ k (hk : k < p.d.shape.insts.length) (args : List Nat) (mc : Sparkle.IR.AST.Module) (st : Stmt),
      (p.d.shape.insts.map (·.2.1))[k]? = some args → st ∈ raw.body →
      Tools.ShippingMachineInst.CallStmt (machNIn p.d.shape) p.d.shape.insts.length
        p.d.shape.layout.slots.length
        ((machPorts p.decl ids cache p.d.shape.binders).map (·.name)) k args mc st →
      Sparkle.IR.Machine.moduleByName D.modules mc.name = some mc →
      ∀ q : Pkg ι dom, P (p.d.shape.insts[k]).1 = some q → CallDec p q k →
      mc.body.all isAssign = true ∧
        ∃ n', CombChildRunN (childMap D.modules) D n' mc (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i) := by
    intro k hk args mc st hargs hst hcs hmod q hq hcd
    have hA : mc.body.all isAssign = true := by
      obtain ⟨_, _, _, iname, _, _, _, _, _, _, _, _, _, hsteq⟩ := hcs
      rw [hsteq] at hst
      exact kidsCombB_assign hkc hst hmod
    refine ⟨hA, ?_⟩
    rcases hx.2 hsimple k hk args mc st hargs hst hcs hmod with ⟨md, hmd, _⟩ | ⟨Dc, hship, hDc⟩
    · -- a memory-origin instance: excluded by `CallDec`'s ordinary origin
      have h1 := hcd.1
      simp only [List.getD_eq_getElem?_getD] at h1 hmd
      rw [h1] at hmd
      cases hmd
    · obtain ⟨_, ⟨q', n', hq', _, hcs'⟩, _⟩ := hship
      have hqq : q' = q := Option.some.inj (hq'.symm.trans hq)
      subst hqq
      exact ⟨n', combChildRunN_of_noClk (callStmt_noClk hcs).1 (hcs'.2 D hDc hmod i)⟩
  -- d2: the call modules' output widths, on THIS witness (`ids`, `cache`), at the intro's `i`
  have hWid : Tools.ShippingGen2Fit.CallOutWidths p.decl p.d p.kD ids cache raw D := by
    intro k args mc st hargs hst hcs hmod outP hout
    have hk : k < p.d.shape.insts.length := by
      have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
    obtain ⟨q, hq, hcd⟩ := hdec k hk
    obtain ⟨-, n', hcomb⟩ := hserve k hk args mc st hargs hst hcs hmod q hq hcd
    obtain ⟨_, _, _, _, hall⟩ := oneOutCall_of_callDec hsimple hcd
    obtain ⟨_, _, o, hsing, _⟩ := hall i bools bits
    -- `CombChildRunN`'s first conjunct (Defs:63): the served module's output is `o`'s port
    have hmo := hcomb.1
    rw [hsing] at hmo
    rw [hmo] at hout
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hout
    -- `hW` at call `k`, read through the index lemma
    have hw := hW k hk q hq o hsing
    rw [Tools.ShippingGen2Fit.binders_drop_at p.d p.kD k (by rw [hIlen]; exact hk)] at hw
    obtain ⟨bn, hbn⟩ : ∃ bn, (p.d.bsIn.drop p.kD)[k]? = some bn :=
      ⟨_, List.getElem?_eq_getElem (by rw [hIlen]; exact hk)⟩
    rw [hbn] at hw
    rw [hout, hbn]
    exact (Option.some.inj hw).symm
  -- AUDIT 2/3: `trace` whole; `F := oneF P p i` after `intro i`
  obtain ⟨envs, hrun, hlen, hobs, hV⟩ := Tools.ShippingGen2Fit.machine_linked_ofBV (ι := ι) (dom := dom)
    (declName := p.decl) (d := p.d) (m := raw) (dsn := D)
    (src := p.src) (ext := p.extS) (extB := p.extBS) (lsrc := p.lsrc)
    nd len rnd rlen llen wired trace hsimple p.kD hkD hI hIlen hSL hSlen hLlen hNIn
    (oneP P p) (oneF P p i) i bools bits T seed st0 mems hsrc hpass hrst hinit
    (by
      -- every call's module computes `oneF P p i k` on `oneP P p k`
      intro k args mc st hargs hst hcs hmod
      have hk : k < p.d.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
      obtain ⟨q, hq, hcd⟩ := hdec k hk
      obtain ⟨hA, n', hcomb⟩ := hserve k hk args mc st hargs hst hcs hmod q hq hcd
      -- AUDIT 4: at the intro's `i bools bits`
      obtain ⟨_, _, _, _, hall⟩ := oneOutCall_of_callDec hsimple hcd
      obtain ⟨_, _, o, hsing, hS, _⟩ := hall i bools bits
      obtain ⟨_, _, outP, _, _, _, hout, _⟩ := hcs
      rw [hsing] at hcomb
      have hfn := childFn_of_combRun hcomb hA hout (fun v _ => hS v)
      have h1 := oneName_some P p hk hq
      refine childFn_mono hfn ?_ ?_
      · intro v hv
        unfold oneP at hv
        obtain ⟨q', hq', hin⟩ := hv
        have hqq : q' = q := Option.some.inj (hq'.symm.trans h1)
        rw [hqq] at hin
        exact hin
      · intro v _
        exact (oneF_of P p i hk hq v).symm)
    (by
      -- the source's call is `oneF P p i k` of its arguments
      intro k args j hargs hj
      have hk : k < p.d.shape.insts.length := by
        have := (List.getElem?_eq_some_iff.mp hargs).1; simpa using this
      obtain ⟨q, hq, hcd⟩ := hdec k hk
      -- AUDIT 4: at the intro's `i bools bits`
      obtain ⟨_, args', hargs', _, hall⟩ := oneOutCall_of_callDec hsimple hcd
      have hae : args' = args := Option.some.inj (hargs'.symm.trans hargs)
      rw [hae] at hall
      obtain ⟨hbnd, hrng, o, hsing, hS, f, hf, hpos⟩ := hall i bools bits
      -- the instance of call `k` (the module's wiring), served as above
      obtain ⟨args'', mc, st, hargs'', hst, hmod, hcs⟩ := wired.2.2.2.2.1 hsimple k hk
      obtain ⟨hA, n', hcomb⟩ := hserve k hk args'' mc st hargs'' hst hcs hmod q hq hcd
      obtain ⟨g, hg⟩ := hS (valsOf (p.lsrc i bools bits) args j)
      have hfg : f j = g 0 :=
        combS_pointwise hcomb hA (valsOf (p.lsrc i bools bits) args) j 0 o f g
          (fun τ' _ => hrng τ') (by simp [hsing]) hf hg
      have hF : oneF P p i k (valsOf (p.lsrc i bools bits) args j) = g 0 := by
        rw [oneF_of P p i hk hq, hg, Option.map_some, Option.getD_some]
      refine ⟨?_, oneP_of P p hk hq (hrng j), hF.trans (hfg.symm.trans (hpos j).symm)⟩
      intro x hx
      obtain ⟨r, hr, hrx⟩ := List.getElem_of_mem hx
      obtain ⟨hl, g', hg'⟩ := hbnd r hr
      rw [← hrx]
      exact ⟨hl, (List.getElem?_eq_some_iff.mp hg').1⟩)
  -- e: the fit on the SAME `envs`, from `CallValues` (same `envs`, same `ids`/`cache`) and `CallOutWidths`
  exact ⟨envs, hrun, hlen, hobs,
    Tools.ShippingGen2Fit.oneOut_ksBoundedRun (declName := p.decl) (d := p.d) (kD := p.kD) (ids := ids)
      (cache := cache) (m := raw) (dsn := D) (regs := regs) (lets := lets) (ext := p.extS) (extB := p.extBS)
      (i := i) (bools := bools) (bits := bits) (envs := envs) wired hsimple hWid hV⟩

/-- PROJECTION CHECK (freeze §3.6): forgetting the fit reproduces `machine_linked_callsServed1`'s conclusion
(OneOut:173). -/
example (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom) {raw : Sparkle.IR.AST.Module} {D : Design}
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hsimple : p.d.shape.instFields = []) (hkD : p.kD ≤ p.d.bsIn.length)
    (hI : ∀ b ∈ p.d.bsIn.drop p.kD, b.2 ≠ .domain)
    (hIlen : (p.d.bsIn.drop p.kD).length = p.d.shape.insts.length)
    (hSL : ∀ b ∈ p.d.slotBs ++ p.d.letBs, b.2 ≠ .domain)
    (hSlen : p.d.slotBs.length = p.d.shape.layout.slots.length)
    (hLlen : p.d.letBs.length = p.d.shape.layout.lets)
    (hNIn : machNIn p.d.shape = ((p.d.bsIn.take p.kD).filter (fun b => b.2 != .domain)).length)
    (hkc : kidsCombB D.modules raw.body = true)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (hW : ∀ k, OneOutWidth P p k) :
    Tools.ShippingMachineShipsHierH.ComposedHB (fun _ _ => True) p.decl p.d p.kD raw D dom p.src p.extS p.extBS :=
  (machine_linked_callsServed1F L P p h hsimple hkD hI hIlen hSL hSlen hLlen hNIn hkc hdec hW).toHB

end Tools.ShippingGen2

/-! ## Block C: consumer (Tools/ShippingSrm33Core.lean:7-21 at f51e68a4, verbatim) -/
namespace Tools.ShippingSrm33
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
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
open Tools.ShippingDesignSV Tools.ShippingDesignSVBounds
open Tools.ShippingSrm25Init (SourceRegsAreSlots)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal

/-- `machine_ships_hierC_noHstR` (Srm33Core:24-189, f51e68a4) with the run-local fit: no `Bd`/`Inv`/`hBd`/`hRI`, no
`Bd b D` antecedent; `composed` is `ComposedNWRegsF`, whose run tail carries `KSBoundedRun` on the same `envs`; the
extracted-input fit comes from `fitX_of_runR` (freeze §3.8 line table; every other line verbatim). -/
theorem machine_ships_hierC_run {n : Nat} (hloc : ∀ D : Design, KSLocal (KSn (childMap D.modules) n))
    (Bnd : CtxBnd)
    (C : Meta.Context → ST.Ref IO.RealWorld Meta.State → Core.Context →
      ST.Ref IO.RealWorld Core.State → Prop)
    {declName : Name} (d : MachineData) {kD : Nat}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {lsrc srcL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {extL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extBL : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    -- the wired endpoint, for the cleanup facts only (its source may be the
    -- fused / sign-normalised one a transported endpoint rewrites)
    (soundL : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design →
      MachineTraceLB declName d m design dom srcL extL extBL lsrc)
    (composed : ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
      {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w' : Void IO.RealWorld}
      {m : Sparkle.IR.AST.Module} {design : Design} {b : Sparkle.IR.AST.Module},
      RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
        (m, design) w' →
      (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule m ∨
        b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule m)) →
      MachineDefines mctx mref cctx cref declName d.shape →
      C mctx mref cctx cref →
      Bnd mctx mref cctx cref w m design → Tools.ConeFold.memFree m.body →
      Tools.ShippingGen2Fit.ComposedNWRegsF n declName d kD m design dom src ext extB
        (fun regs => ∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
          d.shape.layout.slots[k]? = some f → f.width ≤ declWidth b r))
    (houtTy : ∀ o ∈ d.shape.layout.outs, o.ty.bitWidth = o.width)
    (hinitW : ∀ f ∈ d.shape.layout.slots, f.init < 2 ^ f.width)
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : C mctx mref cctx cref)
    -- what the core run provides of the full entry's module, at this run
    (facts : Bnd mctx mref cctx cref w raw D →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b) :
        -- NO checker premise: the run's facts are derived (`facts`)
        -- the run boundary of the children (in the run's contexts)
        Bnd mctx mref cctx cref w raw D →
        ∃ ids : List FVarId, ids.Nodup ∧ ids.length = d.shape.binders.length ∧
        ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
          regs.Nodup ∧ regs.length = d.ss.length ∧
          ∀ (i : ι) (bools : Nat → Signal (dom i) Bool)
            (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
            (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv)
            (kids : String → KT n),
            (∀ t st, t < T → SourceInputs declName (d.bsIn.take kD) ids cache
              (fun j => (extB i bools bits j).val (T - 1 - t))
              (fun j n => (ext i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
            (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
            (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
            (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
              d.shape.layout.slots[k]? = some f → st0 r = f.init) →
            ResetNk n raw D kids →
            (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
            (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
              st0 x < 2 ^ declWidth b x) →
            ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
                (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T
                ⟨st0, mems, kids⟩ = some envsO ∧
              envsO.length = T ∧
              ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
                d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
                (envsO[j]'hj) o.name = f j := by
  intro hBnd
  have hL := soundL hcore entry closes hBnd
  obtain ⟨_, _, _, _, _, _, _, _, _, wired, _⟩ := id hL
  obtain ⟨_, _, _, _, _, _, hlink, houts, _, _, _, _, _, _, _, hclean, _⟩ := wired
  obtain ⟨hb, hw, hi, ho⟩ := hclean houtTy
  obtain ⟨hgate, hwfB, hndB, hself, hOut, hrstIn, hIW⟩ := facts hBnd
  have hOutM := Tools.ShippingHierPremisesBase.outsExtracted_sound hOut
  have hI : Tools.ShippingMachineShipsHier.hasInst b :=
    Tools.ShippingGuardsSound.hasInst_of_hierGate hgate
  have hbr : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw := by
    rcases hpost with h | h
    · exact h
    · exact mergeChecked_inst h hI
  have hbB : b.body = raw.body := by rw [hbr]; exact hb
  have hbW : declWidth b = Tools.ShippingEntrySoundness.weOf raw := by rw [hbr]; exact hw
  have hbI : b.inputs = raw.inputs := by rw [hbr]; exact hi
  have hbO : b.outputs = raw.outputs := by rw [hbr]; exact ho
  have hmf : Tools.ConeFold.memFree raw.body := by
    rw [← hbB]; exact memFree_of_linkedWF _ hwfB
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, hPw, lets, llen, wired, H⟩ :=
    composed hcore hpost entry closes hBnd hmf
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids hsrc hpass hrstZ hclk hinit hreset hinsFit hstX
  have hstR : ∀ r ∈ seqRegs (openFlat b (openIns b) (openOuts b)), st0 r.1 < 2 ^ declWidth b r.1 :=
    Tools.ShippingSrm31.hstR_of_wired_slots hbB (Tools.ShippingSrm28.sourceRegsAreSlots_of_wired_all wired) hinit hinitW hPw
  have hrst : ∀ t st, seedIn b ins t st "rst" = 0 := by
    intro t st
    simp only [seedIn, List.contains_eq_mem, decide_eq_true hrstIn, if_true]
    exact hrstZ t
  obtain ⟨envs, hrun, hlen, hobs, hfitI⟩ := H i bools bits T (seedIn b ins) st0 mems kids hsrc hpass hrst
    hclk hinit hreset
  have hrunB : runModuleTG (KSn (childMap D.modules) n) (declWidth b) (childMap D.modules) b.body
      (seedIn b ins) T ⟨st0, mems, kids⟩ = some envs := by
    rw [hbW, hbB]; exact hrun
  have hfitB : Tools.ShippingGen2Fit.KSBoundedRun (childMap D.modules) b.body envs := by
    rw [hbB]; exact hfitI
  have houtSrc : ∀ (k : Nat) (o : OutField), d.shape.layout.outs[k]? = some o →
      o.name ∈ b.outputs.map (·.name) := by
    intro k o hk
    rw [hbO, houts]
    exact List.mem_map.mpr ⟨_, List.mem_map.mpr ⟨o, List.mem_of_getElem? hk, rfl⟩, rfl⟩
  by_cases hbind : hierBinds b = true
  · -- the optimizer: checked on the extracted interface, or not applied
    have hopt : checkedOptimize b = (if hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b))
        then deinline b (Sparkle.IR.Optimize.optimizeModule b) else b) := by
      unfold checkedOptimize
      simp only [simpleBody_inst hI, not_all_seqOk hI, hbind, Bool.false_eq_true, if_false, if_true]
    by_cases hacc : hierRefineCheck b (deinline b (Sparkle.IR.Optimize.optimizeModule b)) = true
    · -- accepted: the guards give conjuncts 2 and 4, the instance statements 5
      obtain ⟨hwfO, hndO⟩ := Tools.ShippingGuardsSound.deinline_guards
        (o := Sparkle.IR.Optimize.optimizeModule b) hacc hwfB hndB hOut
      have hselfO : Tools.ShippingHierPremisesBase.noSelfRead (childMap D.modules)
          (deinline b (Sparkle.IR.Optimize.optimizeModule b)).body = true :=
        Tools.ShippingChecksDerived2.all_inst_transfer _
          (fun mn iname conns =>
            (Tools.ShippingChecksDerived2.hierRefineCheck_inst_iff hacc mn iname conns).mp)
          (fun st hne => by cases st <;> first | rfl | exact absurd rfl (hne _ _ _)) hself
      have hnofb := Tools.ShippingHierPremisesBase.noSelfRead_sound hselfO
      rw [hopt, if_pos hacc]
      obtain ⟨-, -, envsO, hrunO, hlenO, hcorr⟩ := hierRefineCheck_linked
        (KSn (childMap D.modules) n) (hloc D) (childMap D.modules) hacc
        hwfB hwfO hndB hndO hnofb hOutM ins hinsFit hrstIn hrstZ hrunB
        (Tools.ShippingGen2Fit.fitX_of_runR _ (childMap D.modules) b ins hwfB hIW T _ envs hrunB hfitB hstX) hstR
      refine ⟨envsO, hrunO, by omega, ?_⟩
      intro j hj k o f hk hf
      obtain ⟨p, hp, hpn⟩ := List.mem_map.mp (houtSrc k o hk)
      rw [← hpn, hcorr p hp j hj (by omega), hpn]
      exact hobs j (by omega) k o f hk hf
    · rw [hopt, if_neg hacc]
      exact ⟨envs, hrunB, hlen, hobs⟩
  · -- the check does not bind: the module is shipped as it is
    have hb0 : hierBinds b = false := by simpa using hbind
    rw [Tools.ShippingGuardsSound.checkedOptimize_not_binding hgate hb0]
    exact ⟨envs, hrunB, hlen, hobs⟩

end Tools.ShippingSrm33
