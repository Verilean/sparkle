# S4 run-local fit consumer (replaces consumer 1's `hKSb`) — freeze rev2, FOR REVIEW

- **Issue:** `sparkle-gen2-step` (S4-BD follow-up; S4_BD_RESULT.md "Next").
- **Base:** par/gen2-spec c3ef7eb4 (rev1). Each quoted or copied type names its source file and that file's SHA
  (`git log -1 --format=%h -- FILE` at c3ef7eb4).
- **Design status:** recommended, not shown to be the only design. No compiler mask, no FG premise, no change to `KSBoundedIn`.
- **Built:** nothing. `Tools/ShippingGen2Fit.lean` (§1.4-§1.6) is WRITTEN, NOT BUILT, and `lakefile.lean` has no `lean_lib` entry
  for it yet. One is needed before `kjob lake build Tools.ShippingGen2Fit`. Every other item below is a frozen type, not a proof.

**Changes from rev1 (review of c3ef7eb4).**
1. Every "weakest" claim is deleted (§1, §8). `KSBoundedRun` is stated as SUFFICIENT at Srm33Core:176, together with `hIW` and
   the frame. It is not claimed minimal (§1.4).
2. Every MISSING item has a complete type with its ambient declarations (§2-§4). A copied type either is written out in full or
   gives its base SHA and the exact substitutions.
3. Added: identity checks along the chain (§3.6), projection lemmas back to stage A's types (§3.2-§3.4, §3.6), and
   memory-path compatibility (§4).
4. Group parents are now an UNVERIFIED PLANNED route (§6). Nothing about seq or memory children is claimed as supplied.
5. **Renamed against rev1.** rev1's `ComposedHBV` / `composedNWn_of_HBV` / `ComposedNWV` / `machine_linked_callsServed1V` /
   `composedNWRegs_of_composedNWV` become `ComposedHBF` / `composedNWn_of_HBF` / `ComposedNWF` / `machine_linked_callsServed1F` /
   `composedNWRegsF_of_composedNWF`.
   - Only `machine_linked_ofBV` exposes the VALUE conjunct (c3). From `machine_linked_callsServed1F` on, the chain carries the FIT
     (`KSBoundedRun`) itself.
   - Reason: the width fact (d2) needs the served child of call `k`. That child is available only inside
     `machine_linked_callsServed1`'s proof, on `h`'s witness, after `intro i` (`hserve`, OneOut:179-201). `ChildShips` is stated
     `∀ i`, so outside the `∀ i` there is no `i` to instantiate it with.
   - `KSBoundedRun` mentions neither `KS`, nor the seed, nor `ext`/`extB`. So it passes through `composedNWn_of_HBF` unchanged.

## 1. What `hKSb` is, and the run-local fit

### 1.1 Definition (Tools/ShippingHierOptRun.lean:658-663, 2fd92527)
```lean
def KSBoundedIn {σ : Type} (children : String → Option (Module × WEnv)) (KS : KStep σ)
    (body : List Stmt) (Inv : Module → σ → Prop) : Prop :=
  ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
  children mn = some (child, cwe) →
  ∀ env s cres s', Inv child s → KS child cwe (inConns child.outputs conns) env s = some (cres, s') →
    (∀ p ∈ child.outputs, cres p.name < 2 ^ p.ty.bitWidth) ∧ Inv child s'
```
It quantifies over EVERY `env` and every `Inv`-state. That is why an unmasked pass-through child can fail it (S4_BD_RESULT.md).

### 1.2 Consumer 1's two sites (`machine_ships_hierC_noHstR`, Tools/ShippingSrm33Core.lean:24, f51e68a4)
- :124 `have hKSb := hBd b D hBdb`. This uses the design-level `Bd b D` (:89) and no run.
- :176-178 `fitX_of_run _ (childMap D.modules) b Inv hKSb ins hwfB hndB hIW T _ envs hrunB (… hRI raw D kids hreset …) hstX`.
  - `envs` is the run from `composed`'s `H` (:145), restated on `b` as `hrunB` (:147-149). Its state is `⟨st0, mems, kids⟩` and
    its seed is `seedIn b ins`.
  - Its result is `hierRefineCheck_linked`'s `hfitX` (HierOptRun:545-546).

### 1.3 Inside `fitX_of_run` (HierOptRun:668-763)
`hKSb` is used twice:
- `.1` at :735. This is the child-port bound of the instance-output wire at step 0. `instOutWidthsOk_at hIW` (:734;
  HierOpen:556-561) turns it into `declWidth m x`.
- `.2` at :751. This only carries `Inv` to the next state.

Wires not driven by an instance are handled by the frame (:736-739, :752-761, from `hstX`). So what `fitX_of_run` consumes from
`hKSb` is: on this run, every instance-output wire fits its child port.

### 1.4 `KSBoundedRun` — IMPLEMENTED (unbuilt), Tools/ShippingGen2Fit.lean
```lean
def KSBoundedRun (children : String → Option (Module × WEnv)) (body : List Stmt) (envs : List Env) : Prop :=
  ∀ j (hj : j < envs.length), ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
    children mn = some (child, cwe) → ∀ p ∈ child.outputs, ∀ x,
      conns.lookup p.name = some (.ref x) → (envs[j]'hj) x < 2 ^ p.ty.bitWidth
```
- **Sufficient** at Srm33Core:176. With `hIW` and the frame, it gives `hfitX` (`fitX_of_runR`, §1.5).
- **NOT claimed minimal.** It quantifies over EVERY connected child output wire, but `hfitX` is needed only on the wires in
  `(openIns m).map (·.name)`. Whether a property restricted to `openIns` would also suffice, or would be weaker, is not examined.
- In the other direction, `KSBoundedIn` gives it on a run when given an initial invariant, linked well-formedness and
  instance-name `Nodup` (`ksBoundedRun_of_In`, §4.1, MISSING).

### 1.5 `fitX_of_runR` — IMPLEMENTED (unbuilt), Tools/ShippingGen2Fit.lean
```lean
theorem fitX_of_runR {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv)) (m : Module)
    (ins : Nat → String → Nat) (hwf : linkedWF children m.body = true)
    (hIW : instOutWidthsOk children (declWidth m) m.body = true) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs →
      KSBoundedRun children m.body envs →
      (∀ x ∈ (openIns m).map (·.name), x ∉ bodyInstOuts children m.body →
        s.st x < 2 ^ declWidth m x) →
      ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
        (envs[j]'hj) x < 2 ^ declWidth m x
```
It is a copy of `fitX_of_run` (HierOptRun:668-763, 2fd92527).
- **Dropped:** `Inv`, `hKSb`, `hnd` and the kids-invariant premise.
- **Zero case:** `bodyInstOuts_mem` and the lookup step as at :723-732, but without `linked_consistentKG`. Then
  `rw [instOutWidthsOk_at hIW hmem hc p hp x hl]` and `hB 0 hj …`. Here `envs = envF' :: rest`, and index 0 is `envF'` by `show`,
  as in the original.
- **Successor case:** the recursive call gets `KSBoundedRun … rest` from `hB (j'+1)` (by `simpa` on `(envF' :: rest)[j'+1]`). The
  `.2` block (:744-751) is deleted. The frame-premise block is verbatim.

### 1.6 `posEnc_lt` — IMPLEMENTED (unbuilt), Tools/ShippingGen2Fit.lean
```lean
theorem posEnc_lt (bools : Nat → Bool) (bits : (j : Nat) → (n : Nat) → BitVec n) (pos : Nat)
    (κ : Sparkle.Compiler.Elab.MixedGateBinder) :
    Tools.ShippingMachineEntry.posEnc bools bits pos κ <
      2 ^ (Tools.ShippingMachineEntry.kindTy κ).bitWidth
```
The proof is by cases on `κ`:
- `.domain`: `posEnc` is 0 (Entry:294) and `kindTy` is `.bit` (Entry:232-235). Closed by `Nat.two_pow_pos`.
- `.bool`: `Tools.ShippingMuxLoweringSoundness.encodeBool_lt` (MuxLoweringSoundness:18, `encodeBool b < 2 ^ 1`).
- `.bits n`: `BitVec.isLt`.

**Ambient of Tools/ShippingGen2Fit.lean** (as written):
```lean
import Tools.ShippingHierOptRun
import Tools.ShippingMachineEntry
set_option autoImplicit false
namespace Tools.ShippingGen2Fit
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.HierCheck
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierStateG
open Tools.ShippingHierState Tools.ShippingHierOptLinked
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingHierOptRun
```
This is HierOptRun.lean:27-33 verbatim, plus `open Tools.ShippingHierOptRun`.

## 2. Ambient of the planned chain file `Tools/ShippingGen2FitChain.lean` (MISSING)

The file has three blocks. Every type in §3-§4 says which block it lives in.

**Block A** (generic chain, `namespace Tools.ShippingGen2Fit`):
```lean
import Tools.ShippingGen2Fit
import Tools.ShippingGen2OneOut     -- ExtB, machine_linked_callsServed1, oneP/oneF, CallDec, OneOutCall
import Tools.ShippingSrm33Core      -- consumer 1, ComposedNWRegs (Srm28Regs), RunFacts
set_option autoImplicit false

namespace Tools.ShippingGen2Fit
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Machine (OutField SlotField MachineShape moduleByName)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness (weOf)
open Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked (childMap runModuleH)
open Tools.ShippingMachineDepth
open Tools.ShippingMachineShipsDepth (ResetNk)
```
The copied proofs also need `open Tools.ShippingMachineCompose` and `open Tools.ShippingHierOptRun` for their helper lemmas.
These opens do not change any type below.

**Block B** (package level, `namespace Tools.ShippingGen2`). This is Tools/ShippingGen2OneOut.lean:31-55 at 99f0de5d, verbatim:
```lean
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
```

**Block C** (consumer, `namespace Tools.ShippingSrm33`). This is Tools/ShippingSrm33Core.lean:7-21 at f51e68a4, verbatim:
```lean
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
```

## 3. The chain (all MISSING; types frozen)

### 3.1 Two predicates (Block A)
```lean
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
```

### 3.2 `machine_linked_ofBV` (c3; Block A) and its projection
The type is Tools/ShippingMachineExtB.lean:100-171 at 4c2953c3 (`machine_linked_ofB`) with exactly two substitutions:
- the name;
- the final conclusion `∀ j … (envs[j]'hj) o.name = f j` (:168-171) becomes `(∀ j … = f j) ∧ CallValues …`.

Written out in full:
```lean
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
        CallValues declName d kD ids cache ext extB i bools bits envs
```
**Proof plan.**
- Copy the proof ExtB:172-363 verbatim, except `refine ⟨envs, runModuleH_of_run …, hlenE, hobs⟩` (:307-308). It becomes
  `refine ⟨envs, runModuleH_of_run …, hlenE, hobs, ?_⟩`. Discharge the `CallValues` goal FIRST, then the `?_` of `runModuleH_of_run`.
- `CallValues`: `intro j hj k outW hk hx`.
  - `hinsAt k hk` (:220-225) gives `outW = insNames[k]`.
  - The frame `evalAssigns_frame … hev` (:349), with `instOuts_not_written` (using `calls k hk` and `callStmt_out`), gives
    `envs[j] outW = seed' (T-1-j) stj outW`.
  - `hon (T-1-j) stj k _ hpk` (:242, :357) gives `V k (T-1-(T-1-j))`.
  - `T-1-(T-1-j) = j` follows from `hj` and `hlenE` (:362-363).
- Every ingredient is already in the accepted proof. None uses a new premise.

**Projection** (Block A): `machine_linked_ofB_viaV`. Its statement is ExtB:100-171 at 4c2953c3 VERBATIM, except that the name
`machine_linked_ofB` becomes `machine_linked_ofB_viaV`. Proof:
```lean
  intro i bools bits T seed st0 mems hsrc hpass hrst hinit hchild hval
  obtain ⟨envs, h1, h2, h3, -⟩ := machine_linked_ofBV nd len rnd rlen llen wired trace hsimple kD hkD hI hIlen hSL
    hSlen hLlen hNIn P F i bools bits T seed st0 mems hsrc hpass hrst hinit hchild hval
  exact ⟨envs, h1, h2, h3⟩
```
This checks that dropping the value conjunct gives exactly the accepted type.

### 3.3 `ComposedHBF`, `composedNWn_of_HBF`, `ComposedNWF` (Block A) and their projections
```lean
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
    Tools.ShippingMachineShipsHierH.ComposedHB R declName d kD m dsn dom src ext extB

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

/-- `composedNWn_of_HB` (ExtB.lean:455-479, 4c2953c3) with `ComposedHBF` / `ComposedNWF`; same premises `hB`, `hcomb`. -/
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
    ComposedNWF n declName d kD m dsn dom src ext extB

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
    Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext extB
```
- `ComposedNW` is exactly `composedNWn_of_HB`'s conclusion type (ExtB:466-467). So
  `ComposedNWF.toNW (composedNWn_of_HBF n hC hB hcomb)` has stage A's type.
- Proof of `composedNWn_of_HBF`: ExtB:468-479 verbatim, with `obtain ⟨envs, hrun, hlen, hobs, hfit⟩` and
  `refine ⟨envs, ?_, hlen, hobs, hfit⟩`. `runModuleTG_KSn_of_H` (DepthHR:183-188) returns `some envs` for the SAME `envs`.
- File order: `ComposedNWF` comes before `composedNWn_of_HBF`.

### 3.4 `ComposedNWRegsF` (Block A) and its projection
```lean
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
    ComposedNWRegsF n declName d kD m dsn dom src ext extB P

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
    Tools.ShippingSrm28.ComposedNWRegs n declName d kD m dsn dom src ext extB P
```

### 3.5 d1, e and the index lemma (Block A)
```lean
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
      ((machPorts declName ids cache shape.binders).map (·.name))[machNIn shape + k]? = some x
```
**Proof plan.**
- `wired`'s 6th conjunct (Entry:667-669), at `hsimple` and `hmem`, gives `k args mc` with `moduleByName dsn.modules mn = some mc`
  and `CallStmt … k args mc (.inst mn iname conns)`.
- `childMap_some` (DepthRun) and `hc` give `child = mc`. `moduleByName_name` (Inst) gives `mc.name = mn`.
- `CallStmt` (Inst:190-203) gives:
  - `mc.outputs = [outP]`, so `p = outP`;
  - `names[nIn+k]? = some outW`;
  - `conns = (zip …).map … ++ [(outP.name, .ref outW)]`, with `outP.name` not among the zipped keys (:199). So
    `lookup outP.name = some (.ref outW)` and `x = outW`.
- `k < insts.length` comes from `hargs`.

```lean
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
    KSBoundedRun (childMap dsn.modules) m.body envs
```
**Proof plan.**
- `intro j hj mn iname conns hmem child cwe hc p hp x hl`.
- `oneOut_lookup_callWire wired hsimple hmem hc hp hl` gives `⟨k, args, hargs, hk, hmod, hcall, -, hx⟩`.
- `rw [hV j hj k x hk hx, hW k args child _ hargs hmem hcall hmod p hp]`, then `exact posEnc_lt _ _ _ _`.
- `wired`, `hW` and `hV` are all on ONE `(ids, cache)`. `hV` and the goal are on ONE `envs`.

```lean
/-- Index lemma (d2): call `k`'s result binder in `binders` is `(bsIn.drop kD)[k]`. -/
theorem binders_drop_at (d : MachineData) (kD k : Nat) (hk : k < (d.bsIn.drop kD).length) :
    d.shape.binders[kD + k]? = (d.bsIn.drop kD)[k]?
```
Proof plan: `bsIn := binders.take nIn` (Auto:195). Use `List.getElem?_drop` and `List.getElem?_take_of_lt`, with `kD + k < nIn`
from `hk`.

### 3.6 Identity checks along BV → F → NWF → RegsF → consumer
| quantity | where it is fixed | how it is kept |
|---|---|---|
| `ids`, `cache`, `regs`, `lets`, `wired` | `h`'s witness in `machine_linked_callsServed1F` (as OneOut:175-176) | `machine_linked_ofBV` takes `ids`/`cache` as implicit binders tied to `wired`, so `CallValues` is on them. `CallOutWidths` is built from `wired`/`hserve` on the same witness. `composedNWn_of_HBF` destructures and re-packs the same tuple (as ExtB:468-470). `composedNWRegsF_of_composedNWF` does the same (Srm28:92-94). The consumer refines `TopShips` with that tuple (Srm33Core:135-137) |
| `envs` | `obtain ⟨envs, …⟩ := trace … seed'` in the `machine_linked_ofB` copy (ExtB:275) | It is returned by `refine ⟨envs, runModuleH_of_run …⟩` (:307). `CallValues` and the fit are stated on that `envs`. `runModuleTG_KSn_of_H` returns `some envs` for the SAME list (DepthHR:186-188). In the consumer, the `envs` of :145 is the one in `hrunB` and in `hfitB` |
| `seed` | universally quantified in every `…F` tail | The consumer instantiates `seedIn b ins` once (:145). `fitX_of_runR`'s run is that seed (`hrunB`) |
| time index | `CallValues` at list index `j` reads `.val j` (`T-1-(T-1-j) = j`, ExtB:362-363) | `KSBoundedRun` and `fitX_of_runR` use the same list index `j` |
| `i`, `bools`, `bits` | the tail's `∀ i bools bits` | `CallValues`, `CallOutWidths` (through `hserve` at that `i`), the fit and the observation conjunct all share them |
| raw → b | `composed` is stated for `m := raw` (Srm33Core:136) | `hfitB : KSBoundedRun (childMap D.modules) b.body envs := by rw [hbB]; exact hfitI`, with `hbB : b.body = raw.body` (:129). The children map is `childMap D.modules` in both |

**Projection checks.** Each returns EXACTLY a stage A or accepted type:
- `machine_linked_ofB_viaV` (§3.2) has `machine_linked_ofB`'s type.
- `ComposedHBF.toHB` returns `ComposedHB` (ExtB:36).
- `ComposedNWF.toNW` returns `ComposedNW`, which is `composedNWn_of_HB`'s conclusion type (ExtB:466-467).
- `ComposedNWRegsF.toRegs` returns `ComposedNWRegs`.
- The following check (Block B):
```lean
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
```
  Its type is `machine_linked_callsServed1`'s conclusion (OneOut:173).

### 3.7 Package level (Block B): `OneOutWidth`, `machine_linked_callsServed1F`
`OneOutWidth` does not exist in Lean yet. Its text is S4_CONSUMER_FREEZE.md §5 (approved rev2), unchanged:
```lean
def OneOutWidth (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length) (q : Pkg ι dom), P (p.d.shape.insts[k]).1 = some q →
    ∀ o : OutField, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth
```
```lean
/-- `machine_linked_callsServed1` (OneOut:158-173, 99f0de5d) with premise `hW` added and conclusion `ComposedHBF`. -/
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
    Tools.ShippingGen2Fit.ComposedHBF (fun _ _ => True) p.decl p.d p.kD raw D dom p.src p.extS p.extBS
```
**Proof plan.**
- Copy OneOut:174-256, replacing `machine_linked_ofB` by `Tools.ShippingGen2Fit.machine_linked_ofBV` (same arguments). This gives
  `⟨envs, hrun, hlen, hobs, hV⟩`.
- Return `⟨envs, hrun, hlen, hobs, oneOut_ksBoundedRun wired hsimple hWid hV⟩`, where
  `hWid : CallOutWidths p.decl p.d p.kD ids cache raw D` is built at the intro's `i`:
  - `intro k args mc st hargs hst hcs hmod outP hout`; `k < insts.length` comes from `hargs`.
  - `hdec k` gives `q, hq, hcd`.
  - `hserve k … q hq hcd` gives `CombChildRunN … mc … q.d.shape.layout.outs …`. Its first conjunct is
    `mc.outputs = outs.map …` (Defs:63).
  - `oneOutCall_of_callDec hsimple hcd` at `i bools bits` gives `q.d.shape.layout.outs = [o]` (CallField:171). So `outP.ty = o.ty`.
  - `hW k hk q hq o hsing` and `binders_drop_at p.d p.kD k (hIlen ▸ hk)` give `(kindTy κk).bitWidth = o.ty.bitWidth`, where
    `κk = ((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain`.
- The only new premise relative to stage A is `hW` (S4-WID). It is already a named premise of `oneOut_topShips` (consumer freeze §3).

### 3.8 `machine_ships_hierC_run` (Block C; replaces consumer 1 for this route)
Full type:
```lean
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
    (facts : Bnd mctx mref cctx cref w raw D →
      Tools.ShippingGuardsSound.RunFacts (childMap D.modules) b) :
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
                (envsO[j]'hj) o.name = f j
```
The conclusion after `Bnd … →` is `TopShips`' body (Defs:273-295) at `d := p.d`, `src := p.src`, `ext := p.extS`,
`extB := p.extBS`, `kD := p.kD`.

Line table against Srm33Core.lean at f51e68a4. All other lines are verbatim.

| Srm33Core | change |
|---|---|
| :24 name | `machine_ships_hierC_noHstR` → `machine_ships_hierC_run` |
| :28 (`Bd`, `Inv`), :29 (`hBd`), :30 (`hRI`) | deleted |
| :68 `Tools.ShippingSrm28.ComposedNWRegs` | `Tools.ShippingGen2Fit.ComposedNWRegsF` (same arguments) |
| :88-89 (comment, `Bd b D →`) | deleted |
| :115 `intro hBnd hBdb` | `intro hBnd` |
| :124 `have hKSb := hBd b D hBdb` | deleted |
| :145-146 `obtain ⟨envs, hrun, hlen, hobs⟩ := H …` | `obtain ⟨envs, hrun, hlen, hobs, hfitI⟩ := H …` (same arguments) |
| after :149 | insert `have hfitB : Tools.ShippingGen2Fit.KSBoundedRun (childMap D.modules) b.body envs := by rw [hbB]; exact hfitI` |
| :176-178 | `(Tools.ShippingGen2Fit.fitX_of_runR _ (childMap D.modules) b ins hwfB hIW T _ envs hrunB hfitB hstX) hstR` |

Still used:
- `hIW` (:120, `RunFacts.wid`);
- `hwfB` (:120);
- `hndB` (:120), by `deinline_guards` (:164) and `hierRefineCheck_linked` (:175);
- `hreset` (:146), as the `ResetN` antecedent of `H`.

## 4. The `KSBoundedIn` side and the memory path

### 4.1 `ksBoundedRun_of_In` (MISSING; later in Tools/ShippingGen2Fit.lean, same ambient as §1.6)
```lean
theorem ksBoundedRun_of_In {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    (W : WEnv) (body : List Stmt) (seed : Nat → (String → Nat) → Env) (Inv : Module → σ → Prop)
    (hKSb : KSBoundedIn children KS body Inv)
    (hwf : linkedWF children body = true) (hnd : (instNames body).Nodup) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS W children body seed T s = some envs →
      (∀ mn iname conns, Stmt.inst mn iname conns ∈ body → ∀ child cwe,
        children mn = some (child, cwe) → Inv child (s.kids iname)) →
      KSBoundedRun children body envs
```
What its proof needs, read from `fitX_of_run` (HierOptRun:668-763) and `KSBoundedIn` (:658-663):
- The run itself: induction on `T`, with the step decomposition as at :690-716.
- `hwf` and `hnd`. `linked_consistentKG` (HierOptLinked:268-273) requires `linkedWF` and `(instNames body).Nodup`
  (`Tools.ShippingHierState.instNames`). Per instance, it yields the child step from `s.kids iname` to `kids' iname`, and
  `envF w = cres p.name` on each driven wire.
- The initial invariant on `s.kids` (the last antecedent). It feeds `.1` at index 0, and through `.2` it gives the invariant on
  `kids'` for the recursive call.
- NOT needed:
  - `memFree`: the `memNexts` bind only produces `mems'`, and `kids'` is read from `evalAssignsKG`;
  - `hIW` and the frame;
  - `ResetImpliesInv` itself, which is only the usual supplier of the initial-invariant antecedent (§4.2).

Under the §1.6 opens, `instNames` resolves to `Tools.ShippingHierState.instNames` (HierState:396), not to
`ShippingSrm18Start.instNames`.

### 4.2 `composedNWRegsF_of_In` (Block A, MISSING)
```lean
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
    ComposedNWRegsF n declName d kD m dsn dom src ext extB P
```
**Proof plan.**
- Destructure `h`.
- `hwf` comes from `wired` (its linkedOk conjunct with `linkedOk_eq`, as ExtB:471-473).
- In the tail: `obtain ⟨envs, hrun, hlen, hobs⟩`, then
  `ksBoundedRun_of_In _ _ _ _ seed Inv hKSb hwf hnd T ⟨st0, mems, kids⟩ envs hrun (hRI m dsn kids hreset)`.
- `hreset` is the tail's `ResetN` antecedent, which is literally `ResetNk n m dsn kids` (ShipsDepth:245-248).

### 4.3 Compatibility with the memory path (`memParent_topShips`, Tools/ShippingGen2MemTop.lean:45-101, 158b70d2)
- **No change.** `memParent_topShips` keeps calling consumer 1 `machine_ships_hierC_noHstR` (MemTop:84-101) with:
  - `Bd := kidsMem`;
  - `Inv := memInvN (n+1)`;
  - `hBd := memKSn_boundedIn` (MemBd:54);
  - `hRI := resetNk_memInvN` (MemBd:82).

  Consumer 1 is neither deleted nor edited. This freeze only ADDS `machine_ships_hierC_run`.
- **Optional single-consumer route (UNVERIFIED, planned only).**
  - `composed` would become
    `composedNWRegsF_of_In (memInvN (n+1)) (composedNWRegs_of_composedNW _ hNW hP) (memKSn_boundedIn D.modules raw.body hkm (n+1))
    (resetNk_memInvN (n+1)) hnd`, with `hkm : kidsMem (childMap D.modules) raw.body = true` and
    `hnd : (instNames raw.body).Nodup`.
  - Inside MemTop's `composed` callback these two facts are available only on `b'`: `core_kidsMem_ranAM` (:101) is on `b`, and
    `RunFacts.ndB` is on `b'` via `factsB`.
  - Moving them to `raw.body` needs `b'.body = raw.body` (Srm33Core:117-129 derive it from the trace's cleanup conjunct). That
    is not done.
  - Until then, the memory path stays on consumer 1.

## 5. Supply chain order (one-output route)
| # | fact | status |
|---|---|---|
| a | input fit `hinsFit`, `hstX` (TopShips antecedents) | EXISTING; not on the instance-output chain |
| b1 | let range `Pkg.lsrc_hl` (Gen2Pkg:102-105) | EXISTING |
| b2 | argument `InRange`: `CallDec`/`OneOutCall` (Defs:110; CallField:170) | EXISTING |
| b3 | argument wires = source lets (`hargVals`, ExtB:321-342) | EXISTING |
| c1 | child meaning `ChildFn` via `hserve` / `childFn_of_combRun` (OneOut:179-235) | EXISTING |
| c2 | child output = `posEnc` of the call-result binder (`combS_pointwise` + `CallDec`, OneOut:236-256) | EXISTING |
| c3 | wire value on the run: `CallValues` from `machine_linked_ofBV` (§3.2) | MISSING (copy) |
| c4 | `posEnc_lt` (§1.6) | IMPLEMENTED, unbuilt |
| d1 | `oneOut_lookup_callWire` (§3.5) | MISSING |
| d2 | `CallOutWidths` inside `machine_linked_callsServed1F`, from `hW` + `CombChildRunN`.1 + `binders_drop_at` (§3.5, §3.7) | MISSING; needs `hW` (G-ONEOUT-WID) |
| e | `oneOut_ksBoundedRun` (§3.5) → `ComposedHBF` → `ComposedNWF` → `ComposedNWRegsF` | MISSING |
| f | `fitX_of_runR` (§1.5) in `machine_ships_hierC_run`, with `hIW = RunFacts.wid` | lemma IMPLEMENTED (unbuilt); consumer MISSING |

**Order:** b1 → b2 → b3 → c1 → c2 → c3 → c4 → d1/d2 → e → f.
- Neither c1 nor c3 uses the parent's fit or a range of the child's output. `ChildFn`'s premise is b2, which comes from the source.
- The parent's fit (f) is a consequence and is never assumed.
- The child's own `TopShips` antecedents are not used. `CombChildRunN` (Defs:71) takes only the argument `InRange`.

**Alternative source-output range (not recommended).** It would be a `Pkg.src_lt`, which does not exist: `Pkg.src_length` and
`Pkg.src_get` (CombKid:56/:79) give only the shape. The `posEnc` route (c2+c4) needs no new source fact.

**Rejected variant (records a stop).** Stating the fit against `declWidth b x` would drop `hIW`/`hW`.
- It would need `declWidth b x = (kindTy (binders[kD+k]).2).bitWidth`, keyed on the SAME `k`.
- The only supplier pattern is `core_callPorts_ranA` (Tools/ShippingParentRunFactsA.lean:410-437, :557-562). It requires
  `hfne : instFields ≠ []` (:418), and it is stated over the `ran` witness, not over the trace's `ids`/`cache`.
- Nothing supplies a match of `k` across the two witnesses.

## 6. Group parents (`closeInstsG`, `instFields ≠ []`) — UNVERIFIED PLANNED ROUTE
Nothing in this section is supplied, typed or checked. It only records where a group copy would start.
- `machine_linkedTG_of` (Tools/ShippingMachineLinkedTG.lean:30) builds a `V`/`seed'` (LinkedTG:185-189) like ExtB's. A copy that
  exposes a value conjunct is PLANNED. Whether its frame argument carries over to children with state (seq) or to memory children
  is NOT checked.
- d1 for groups would come from `MachineWired`'s `CallStmtG` clause (Entry, `instFields ≠ []`) and `connsG` (LinkedT:28-34).
  `group_lookup_callWire` is not stated.
- d2 for groups: `hkidW` (ParentRunFactsA:587-591; `hkidW_of_dataA` :612) is a candidate. Whether it fits a group `CallOutWidths`
  is not checked.
- Not claimed:
  - that sequential or memory children's outputs equal a parent binder's `posEnc` on the run;
  - that their widths are supplied;
  - that the producers (`machine_linkedT_callsRNA`, DepthRunRA:142, :214; `machine_linkedT_callsServed`, Gen2Consumer:30) can be
    copied without new premises.
- Memory-only group parents stay on consumer 1 (§4.3).

## 7. Stop conditions and coverage obligations
- **G-ONEOUT-WID (unchanged):** `∀ k, OneOutWidth P p k` has no supplier (consumer freeze §5). It is needed twice: by d2
  (`machine_linked_callsServed1F`'s `hW`) and by `RunFacts.wid` (`core_instOutWidthsOk_oneA`, MISSING, consumer freeze §5).
- **G-SERVED (unchanged):** `h` / `ServedP (ShipsRes L P)` (Defs:251, not built).
- **S4-MEM case restriction (unchanged):** `hnomem` and `hdec` in the `CallDec`-only form.
- **Cross-witness width:** a stop for the rejected variant only (§5).
- **No new stop was found for the one-output route** while fixing the types of §3.
  - Every type above is fixed without a new premise beyond `hW`, which is already a named stage-B premise.
  - No existing guarantee changes. Consumer 1 and stage A are unchanged.
  - None of this was checked by a build.
- **lakefile:** `Tools.ShippingGen2Fit`, and later `Tools.ShippingGen2FitChain`, need `lean_lib` entries before they can be built.

## 8. Not claimed
- Nothing is built. The MISSING items are designs. The three IMPLEMENTED items are written but not compiled.
- `KSBoundedIn` is neither refuted nor proved for any real child.
- No minimality of `KSBoundedRun` is claimed: it bounds every connected output wire, while `hfitX` needs only the `openIns` wires.
- Nothing about group parents (§6) is claimed.
