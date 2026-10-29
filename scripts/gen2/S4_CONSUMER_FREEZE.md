# S4 consumer (G-ONEOUT): one-output parents on the A boundary — freeze rev2, FOR REVIEW

- **Issue:** `sparkle-gen2-step` (S4 of STEP_IFACE_FREEZE.md rev3 §4, approved; CALLFIELD_RESULT.md, approved).
- **Branch:** `par/gen2-spec`. rev1 = ee4f03b1 (changes_requested R1, R2, S4-WID, S4-BD, S4-MEM, integration). Lean read at
  ee4f03b1 (no `.lean` file changed since ffd283ce: `git diff --stat ffd283ce ee4f03b1` lists this file only).
  Read-only survey. No Lean is changed by this document; nothing in it is proved or built.
- **Scope:** parents with `instFields = []`, `insts ≠ []` and `slots ≠ []`, closed by `closeInsts` (Sparkle/IR/Machine.lean:396-427),
  selected at Sparkle/Compiler/Elab.lean:5261-5262 (`shape.instFields.isEmpty` → `closeInstsM`). Slotless one-output parents are S5.
- **rev2 changes:** §2 complete signatures with ambient declarations, diff limited to `extB`, compatibility checks, AUDIT clause (R1);
  §3 stages A/B/C, `oneOut_topShips`/`oneOut_step` removed from "provable from existing facts" (R2); §5 S4-WID typed relation and
  supplier survey; §6 S4-BD risk-check plan; §7 S4-MEM case restriction and probe; §8 integration note. Also corrected: rev1's
  `fun _ _ _ _ _ _ _ _ _ _ _ _ => trivial` for `BoundH` had 12 binders (13 needed); now `by intros; trivial`.

## 1. Selecting the combinational branch (facts of the parent's run)
- **The refusal.** `instStmt` (Machine.lean:272) returns `none` when `mc.inputs.any (fun p => p.name == "clk" || p.name == "rst")`
  (Machine.lean:278), and requires `mc.outputs = [outP]` (Machine.lean:280). It checks NO width (Machine.lean:272-292).
- **`CallStmt` records it.** `Tools.ShippingMachineInst.CallStmt` (Tools/ShippingMachineInst.lean:190-203) has
  `(mc.inputs.any (fun p => p.name == "clk" || p.name == "rst")) = false` and `mc.outputs = [outP]`.
- **Where the consumer gets `CallStmt`.** From `MachineWired`'s one-output clauses (Tools/ShippingMachineEntry.lean:664-669), with the
  trace's `machPorts declName ids cache` names — the same `CallStmt` as in `Served1P` (Tools/ShippingGen2Defs.lean:231-240) and
  `machine_linked_of` (Tools/ShippingMachineCompose.lean:590-595).
- **Assignment-only children.** `closeInsts_kidsComb` (Tools/ShippingChildServe.lean:248) on the closing of `core_closeInstsA`
  (Tools/ShippingParentDesignA.lean:152), on `MachineRanA` from `machineRanA_of_runJQC` (Tools/ShippingRanABridge.lean:38);
  `kidsComb_of_B` (Tools/ShippingMachineDepthHR.lean:31) converts.
- **C3 / C2.** `not_seq_and_comb`, `childRunN_iff_seq` (Tools/ShippingGen2AComb.lean:23, :28). No lemma for the `"clk" ∉` direction.

**Missing (pure, small)** — in the new file `Tools/ShippingGen2OneOut.lean` (ambient: §2.5), `namespace Tools.ShippingGen2`:
```lean
theorem callStmt_noClk {nIn kI n : Nat} {names : List String} {k : Nat} {args : List Nat}
    {mc : Sparkle.IR.AST.Module} {st : Stmt}
    (h : Tools.ShippingMachineInst.CallStmt nIn kI n names k args mc st) :
    "clk" ∉ mc.inputs.map (·.name) ∧ "rst" ∉ mc.inputs.map (·.name)
theorem combChildRunN_of_noClk {children : String → Option (Sparkle.IR.AST.Module × WEnv)} {dsn : Design} {n : Nat}
    {mc : Sparkle.IR.AST.Module} {bsC : List (Name × MixedGateBinder)} {outsC : List OutField}
    {S : (Nat → List Nat) → List (Nat → Nat)}
    (hclk : "clk" ∉ mc.inputs.map (·.name)) :
    ChildRunN children dsn n mc bsC outsC S → CombChildRunN children dsn n mc bsC outsC S
  -- fun h => h.elim (fun hs => absurd hs.2.2.1 hclk) id   (as childRunN_iff_seq, AComb:28-30)
theorem kidsCombB_assign {ms : List Sparkle.IR.AST.Module} {body : List Stmt} {mn iname : String}
    {conns : List (String × Sparkle.IR.AST.Expr)} {c : Sparkle.IR.AST.Module}
    (h : kidsCombB ms body = true) (hst : Stmt.inst mn iname conns ∈ body)
    (hc : moduleByName ms mn = some c) : c.body.all isAssign = true
```

## 2. The served consumer and the `extB` copies (R1)

### 2.1 Obstruction
`machine_linked_of` (Compose.lean:538), `machine_linked_callsRA` (Tools/ShippingMachineComposeRA.lean:72), `ComposedH`
(Tools/ShippingMachineShipsHierH.lean:33) and `composedNWn_of_H` (DepthHR:208) fix `extB := fun _ bools _ => bools`: `(bools j).val`
at Compose.lean:556 (trace), :583 (conclusion), `posEnc (fun p => (bools p).val j)` at Compose.lean:601 and :672 (proof, `let V`),
ComposeRA:84 (trace type) and :100, ShipsHierH:49, and DepthHR:217-218 (conclusion). The package trace uses `p.extBS`
(Tools/ShippingGen2Pkg.lean:67-71), as do `StepStmt` (Defs:311-312), `CallDec` (Defs:111-113), `OneOutCall`
(Tools/ShippingGen2CallField.lean:174-175). `ComposedNW` (Tools/ShippingMachineDepthRun.lean:34-63) already takes `extB`.

**Rule for the copies.** Each copy is the accepted declaration's text with ONE new binder `extB` (the type of `ComposedNW`'s `extB`,
DepthRun:41-42), inserted right after `ext`, with the same implicitness as `ext`, and every `(bools x).val` read of an input signal
replaced by `(extB i bools bits x).val`. Nothing else changes: binder names, order, implicitness, conclusion. They are placed by
REOPENING the original namespace in a new file, with the original file's `open`s copied verbatim, so every name resolves as in the
original and the proof text can be copied. Proposed new file `Tools/ShippingMachineExtB.lean` (names checked unused by grep):
```lean
import Tools.ShippingMachineCompose
import Tools.ShippingMachineShipsHierH
import Tools.ShippingMachineDepthHR
```
None of the three original files declares a `variable`; `machine_linked_of` sits in `section Linked` (Compose.lean:523-923).

### 2.2 `ComposedHB` — `ComposedH` (ShipsHierH:33-66) with `extB`
```lean
namespace Tools.ShippingMachineShipsHierH
-- ShipsHierH.lean:18-28, verbatim
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

def ComposedHB (R : Nat → Sparkle.IR.AST.Module → Prop) (declName : Name) (d : MachineData) (kD : Nat)
    (m : Sparkle.IR.AST.Module) (dsn : Design) {ι : Type} (dom : ι → DomainConfig)
    (src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat))
    (ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (extB : (i : ι) → (Nat → Signal (dom i) Bool) →                                  -- NEW binder
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
        (fun j => (extB i bools bits j).val (T - 1 - t)) (fun j n => (ext i bools bits j n).val (T - 1 - t))   -- was (bools j)
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

/-- CHECK 1: at the identity `extB` the copy IS the accepted definition (the only difference is the β-redex
`(fun _ bools _ => bools) i bools bits j`). -/
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
```
Diff from ShipsHierH:33-66: the `extB` binder and line 49. Both are plain `def`s, so `rfl` is expected to elaborate; if it does not,
the fallback `by unfold ComposedHB ComposedH; rfl` is tried and the failure of plain `rfl` is REPORTED (an `Iff` is not a silent
substitute).

### 2.3 `machine_linked_ofB` — `machine_linked_of` (Compose.lean:538-606) with `extB`
```lean
namespace Tools.ShippingMachineCompose
-- Compose.lean:17-19, verbatim
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.IR.Reorder (refsOf writesOf stmtWrites)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingMachineLinked
section LinkedB
-- Compose.lean:524-528 (section Linked), verbatim
open Lean Sparkle.Compiler.Elab Tools.ShippingMachineEntry Tools.ShippingMixedEntrySoundness
open Tools.ShippingMixedSourceBridge Tools.ShippingMachineAuto
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.Machine (SlotField OutField)
open Tools.ShippingEntrySoundness (weOf)

theorem machine_linked_ofB {declName : Name} {d : MachineData} {m : Sparkle.IR.AST.Module} {dsn : Design}
    {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →                                  -- NEW binder
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
        (fun j => (extB i bools bits j).val (T - 1 - t))                                -- was (bools j), line 556
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
        (fun j => (extB i bools bits j).val (T - 1 - t)) (fun j n => (ext i bools bits j n).val (T - 1 - t))   -- was (bools j), line 583
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
          posEnc (fun p => (extB i bools bits p).val j) (fun p n => (ext i bools bits p n).val j) (kD + k)   -- was (bools p), line 601
            (((d.bsIn.drop kD)[k]?.map (·.2)).getD .domain)) →
      ∃ envs, runModuleH (weOf m) (childMap dsn.modules) m.body seed T st0 mems = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j
```
Diff from Compose.lean:538-606: the `extB` binder and the three marked lines. Proof: Compose.lean:607-800 copied, with the
`let V` at :671-673 reading `(extB i bools bits p).val j`; `sourceInputs_extend` (Compose.lean:370) is applied to `hin` at :714
unchanged (generic in the Bool reader). `P`, `F` stay OUTSIDE `i`, as in the original.

```lean
/-- CHECK 2: the accepted theorem is the copy at the identity `extB`. -/
theorem machine_linked_of_viaB
    -- binders and statement: Compose.lean:538-606 character for character (the ACCEPTED text, reproduced unchanged)
    := machine_linked_ofB (extB := fun _ bools _ => bools) nd len rnd rlen llen wired trace hsimple kD hkD hI hIlen hSL hSlen
      hLlen hNIn P F
end LinkedB
end Tools.ShippingMachineCompose
```
The comment stands for an EXISTING text cited by lines that the check must reproduce verbatim; it is not an elided new signature.
The proof term uses no tactic and no `show`: at `extB := fun _ bools _ => bools` each marked line β-reduces to the original, so the
conclusion of the copy at the identity is the original conclusion (definitional, checked by elaboration of this term).

### 2.4 `composedNWn_of_HB` — `composedNWn_of_H` (DepthHR:208-227) with `extB`
```lean
namespace Tools.ShippingMachineDepthHR
-- DepthHR.lean:15-24, verbatim
open Lean Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingEntrySoundness
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierState
open Tools.ShippingHierStateG Tools.ShippingMachineLinked Tools.ShippingHierOptRunH
open Tools.ShippingMachineDepthH Tools.ShippingHierSVRunH
open Sparkle.IR.Reorder (writesOf)
open Sparkle.IR.RegDedup (declWidth isAssign)

theorem composedNWn_of_HB (n : Nat) {R : Nat → Sparkle.IR.AST.Module → Prop} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Sparkle.IR.AST.Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →                                  -- NEW binder
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (hC : Tools.ShippingMachineShipsHierH.ComposedHB R declName d kD m dsn dom src ext extB)   -- was ComposedH … ext
    (hB : BoundH R declName d m dsn) (hcomb : kidsComb dsn.modules m.body = true) :
    Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext
      extB                                                                            -- was (fun _ bools _ => bools)
  -- proof: DepthHR:219-227 verbatim (`H i bools bits T seed st0 mems hsrc …`: both sides now read extB)

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
    Tools.ShippingMachineDepthRun.ComposedNW n declName d kD m dsn dom src ext (fun _ bools _ => bools) :=
  composedNWn_of_HB n (extB := fun _ bools _ => bools)
    ((Tools.ShippingMachineShipsHierH.composedHB_id R declName d kD m dsn dom src ext).symm ▸ hC) hB hcomb
end Tools.ShippingMachineDepthHR
```
Diff from DepthHR:208-218: the `extB` binder, `hC`'s type, the conclusion's last argument.

**Existing declarations stay unchanged; these are new helpers only.** `machine_linked_callsRA` (ComposeRA:72-125) is NOT copied: its
`P F` sit outside `i`, its `X` is `ServedRealA O`, and its `hfn` quantifies over every run of the callee — none of that fits the served
consumer. It is the proof TEMPLATE only (ComposeRA:110-113 `obtain`/`refine`/`intro`, :121-124 `hx.2` case split); AUDIT item 5
(§2.6) lists every difference.

### 2.5 The served consumer (new file `Tools/ShippingGen2OneOut.lean`)
```lean
import Tools.ShippingGen2CallField
import Tools.ShippingGen2CombKid
import Tools.ShippingGen2AComb
import Tools.ShippingGen2MemShips
import Tools.ShippingMachineExtB
set_option autoImplicit false
namespace Tools.ShippingGen2
-- Defs.lean:16-33, verbatim
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
-- Defs.lean:122 (for `dv` in §3)
open Tools.ShippingChildBndCore (cv dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- The argument condition of call `k`: in range for the callee package's ports (`Pkg.ports`, Pkg.lean:80-81). -/
def oneP (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) (v : List Nat) : Prop :=
  ∃ q, P ((p.d.shape.insts.map (·.1))[k]?.getD .anonymous) = some q ∧ InRange v q.ports

/-- The function of call `k` at index `i`: the callee's only output, at time 0, on the constant argument stream. -/
noncomputable def oneF (P : Pkgs ι dom) (p : Pkg ι dom) (i : ι) (k : Nat) (v : List Nat) : Nat :=
  match P ((p.d.shape.insts.map (·.1))[k]?.getD .anonymous) with
  | some q => ((q.S i (fun _ => v))[0]?.map (· 0)).getD 0
  | none => 0

theorem machine_linked_callsServed1 (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
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
      ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) :
    Tools.ShippingMachineShipsHierH.ComposedHB (fun _ _ => True) p.decl p.d p.kD raw D dom p.src p.extS p.extBS
```
`Laws`, `Pkgs`, `Pkg`, `ShipsRes`, `ServedP`, `CallDec` are `Tools.ShippingGen2.*` (current namespace). `hdec` is the STRENGTHENED
decoding (no `MemDec` disjunct): a case restriction, §7.

### 2.6 Proof route and AUDIT clause
```lean
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, hx, trace⟩ := h      -- ONE witness
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, ?_⟩
  intro i bools bits T seed st0 mems hsrc hpass hrst hinit _
  exact Tools.ShippingMachineCompose.machine_linked_ofB nd len rnd rlen llen wired trace hsimple p.kD hkD hI hIlen hSL hSlen
    hLlen hNIn (oneP P p) (oneF P p i) i bools bits T seed st0 mems hsrc hpass hrst hinit ?hfn ?hcalls
```
- **`?hfn`, per `(k, args, mc, st)`** (the `intro`'s `bools bits` in scope). `hx.2 hsimple k hk args mc st hargs hst hcs hmod`
  (`Served1P`). Left disjunct: `CallDec`'s `child? = none` contradicts `child? = some md` (as ComposeRA:122). Right disjunct:
  `ShipsRes L P c (mc, Dc)` (Defs:135-136) = `RealChildA L.O c (mc, Dc) ∧ ∃ q' n, P c = some q' ∧ q'.decl = c ∧ ChildShips q' n mc Dc`;
  `q' = q` from `hdec`. `ChildShips` (Defs:87-90) at `dsn := D` (Served1P's `∀ g ∈ Dc.modules, …` and `hmod`) gives
  `ChildRunN (childMap D.modules) D n mc (q.d.bsIn.take q.kD) q.d.shape.layout.outs (q.S i)`; `callStmt_noClk hcs` +
  `combChildRunN_of_noClk` give `CombChildRunN`; `q.d.shape.layout.outs = [o]` from `oneOutCall_of_callDec hsimple` (CallField:177) at
  `i bools bits`. `childFn_of_combRun` (Tools/ShippingGen2CombKid.lean:174) with `hA := kidsCombB_assign hkc …`, `hout` from
  `CallStmt`, `hS` from `OneOutCall`'s `∀ v, ∃ g, (q.S i (fun _ => v))[0]? = some g`; result `ChildFn mc (oneP P p k) (oneF P p i k)`
  after rewriting `oneP`/`oneF` with `P c = some q`. The height `n` is the one `ShipsRes` carries; S4-b/S4-c hold at every `n`.
- **`?hcalls`, per `(k, args, j)`.** `OneOutCall` at `i bools bits`: argument bounds, `InRange (valsOf …) q.ports` (gives `oneP`), and
  `f` with `(q.S i (valsOf (p.lsrc i bools bits) args))[0]? = some f` and `posEnc (p.extBS …) … = f τ`. `combS_pointwise` (CombKid:205)
  with `vals := valsOf …`, `τ := j`, `g` from `hS` gives `f j = g 0 = oneF P p i k (valsOf … j)`. Its `CombChildRunN` is that of call
  `k`'s served instance: `MachineWired`'s clause (Entry:664-666) gives `(args, mc, st)` with `CallStmt`, then `Served1P` as above.

**AUDIT (to be checked on the built proof and stated in its header):**
1. `wired`, `hx` (= `ServedP (ShipsRes L P) p.decl p.d.shape raw D ids cache`) and `trace` come from the SAME `obtain` of the ONE
   `MachineTraceLBX` `h`. The `ids`/`cache` in `Served1P`'s `machPorts … ids cache` names and in `machine_linked_ofB`'s callback
   `CallStmt` are those `ids`/`cache`, definitionally (no rewriting). No second trace; no `Served1P` from another witness.
2. `trace` is passed WHOLE (its `∀ i bools bits T seed st0 mems` intact); it is not specialised before. `machine_linked_ofB`
   instantiates it at the same `i bools bits` and at its own extended seed (Compose.lean:711), which needs the `∀ seed` inside it.
3. `F := oneF P p i` is chosen AFTER `intro i`; the conclusion is used at that `i` only. `oneP` does not depend on `i`.
4. `OneOutCall`/`CallDec` are used at the `intro`'s `i bools bits`, never at a chosen element of `ι` (no `Nonempty ι`).
5. Differences from `machine_linked_callsRA` (the template): `X := ServedP (ShipsRes L P)` for `ServedRealA O`; `extB := p.extBS`;
   `hcalls`/`hfn` discharged (from `hdec` and the served evidence), not premises; `P F := oneP P p, oneF P p i`, chosen per `i`;
   premise `hkc` added; conclusion `ComposedHB … p.extBS` for `ComposedH`. Nothing else.

## 3. Stages (R2)
A closing (a proof of one stage) does NOT count as completion of a later stage, of G-ONEOUT, or of M2.

### Stage A — served consumer → `ComposedNW` → the parent's `ChildShips`
Not blocked by S4-WID/S4-BD; uses the §7 case restriction (`hdec`). Targets, in `Tools/ShippingGen2OneOut.lean`:
```lean
theorem oneOut_composedNW (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    Tools.ShippingMachineDepthRun.ComposedNW n p.decl p.d p.kD raw D dom p.src p.extS p.extBS

theorem oneOut_childShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p) (hext : ExtInS p)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (n : Nat) :
    ChildShips p (n + 1) b D
```
`MemParentDataOk`, `ExtInS`: Tools/ShippingGen2MemParent.lean:38-44, 46-50. Despite the name, `MemParentDataOkB`'s five rows (`ok`,
`callsOk p.kD`, slot count, `outTy`, `domB`) say nothing about memories.

**Evidence plan.**
- Data: `MemParentDataOk.rows` (Tools/ShippingGen2MemData.lean:16), `data_hkD`/`data_hIlen`/`data_hSL`/`data_hSlen`/`data_hLlen`/`data_hNIn`
  (MemData:37-66), as MemShips:51-56. `hI` from `domB` (`bsIn := binders.take nIn`, Tools/ShippingMachineAuto.lean:195, so
  `bsIn.drop kD` is a prefix of `binders.drop kD`): small missing lemma `data_hI`.
- `hkc`: `ranA := machineRanA_of_runJQC L.O hA L.T ran`; `core_closeInstsA L.O p.d hins hsimple ranA` (ParentDesignA:152) exposes the
  closing; `closeInsts_kidsComb` (ChildServe:248).
- `oneOut_composedNW := composedNWn_of_HB n (machine_linked_callsServed1 L P p h hsimple hkD hI hIlen hSL hSlen hLlen hNIn hkc hdec)
  (by intros; trivial) (kidsComb_of_B hkc)`.
- `oneOut_childShips`: as `memParent_childShips` (Tools/ShippingGen2MemShips.lean:39-90), but the closing branch is `hf0`
  (`closeInsts_acyclic`, ChildServe:200) instead of `closeInstsG_acyclic`; `hI0` from `hins`; `hEA` as MemShips:76-84; then
  `Or.inl (Tools.ShippingGen2C6.seqChildRunN_of_composedNW_run n houtTy (ok_outNameOk p.d hok) hsl hI0 hkD hIlen hSL hSlen hLlen hNIn
  hext.1 hext.2 i (oneOut_composedNW …) hpost hEA acyc.1)` (C6:28; it handles `instFields = []`, C6:64-68).

**Residues of stage A (premises without a supplier here):** `h` (G-SERVED, `ServedShipsStmt`, Defs:251, not built); `hdec` in the
strengthened form (§7 case restriction); `hext : ExtInS p` (per package, as for M2-a). New lemmas: §1's three, `data_hI`, the three
copies with checks, `oneP`/`oneF`, `machine_linked_callsServed1`.

### Stage B — width/range supplied, then `TopShips` (BLOCKED on S4-WID and S4-BD)
Consumer 1, `machine_ships_hierC_noHstR` (Tools/ShippingSrm33Core.lean:24), as in `memParent_topShips` (Tools/ShippingGen2MemTop.lean:45-102):
`soundL := (Pkg.trace L.O L.T hA p ran).toLB` (TraceX:863); `composed` from stage A's `ComposedNW` via `composedNWRegs_of_composedNW`
(Tools/ShippingSrm28Regs.lean:77) + `hWd_of_wired` (Tools/ShippingSrm32Width.lean:28); `facts : RunFacts` (Tools/ShippingGuardsSound.lean:314-322):
`gate`/`ndB`/`self`/`outs`/`rst` from `core_runFactsHA` (ParentDesignA:494; needs `hnomem` — the §7 case restriction), `wfB` from
`core_linkedWF_ranA` (Tools/ShippingParentTailsA.lean:197). Two needed facts have NO supplier, so the target is CONDITIONAL, with the
blockers as named premises:
```lean
theorem oneOut_topShips (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hnomem : ∀ x ∈ p.d.shape.instTagged,
      x.2.child?.isNone = true ∧ (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true)        -- §7 case restriction
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)   -- §7
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hW : ∀ k, OneOutWidth P p k)                                                                      -- S4-WID: no supplier (§5)
    (hBd : ∀ n, Tools.ShippingHierOptRun.KSBoundedIn (childMap D.modules) (KSn (childMap D.modules) n) b.body
      (fun _ _ => True))                                                                               -- S4-BD: no supplier (§6)
    (n : Nat) :
    TopShips p (n + 1) p.decl b raw D
```
Even with `hW`, `RunFacts.wid` needs a NEW one-output lemma (`core_instOutWidthsOk_ranA`, Tools/ShippingParentRunFactsA.lean:566,
requires `hfne : instFields ≠ []`, :575; §5). Proving this conditional statement is NOT completion of stage B: stage B is complete only
when `hW` and `hBd` are discharged from the run or the data.

### Stage C — `StepStmt` case coverage (BLOCKED on S4-MEM)
`OneOutStepStmt` (§4) covers `StepStmt`'s one-output-with-slots case only when its `hnomem` row and strengthened `hdec` are derived
from `StepStmt`'s premises (`MemDec ∨ CallDec`, Defs:309-310) or shown unnecessary. §7 gives the probe; until it resolves, stage C is open.

## 4. The one-output step statement (intermediate, ordinary-only case)
```lean
def OneOutDataOkB (p : Pkg ι dom) : Bool :=
  MemParentDataOkB p &&                                                          -- MemParent.lean:38-42 rows
  p.d.shape.instTagged.all (fun x => x.2.child?.isNone && (Sparkle.Compiler.MachMemory.memChild? x.1).isNone)  -- hnomem: CASE RESTRICTION

def OneOutStepStmt {mref cref} (L : Laws mref cref) (P : Pkgs ι dom) (DataOk : Pkg ι dom → Prop) : Prop :=
  ∀ (p : Pkg ι dom) (mctx : Meta.Context) (cctx : Core.Context) (w w1 : Void IO.RealWorld)
    (raw b : Sparkle.IR.AST.Module) (D : Design),
    P p.decl = some p → DataOk p → OneOutDataOkB p = true → ExtInS p →
    p.d.shape.insts ≠ [] → p.d.shape.instFields = [] → p.d.shape.layout.slots ≠ [] →
    AdmCtx L.O.quiet mctx cctx → JQC L.O (dv w) w →
    RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1 →
    (b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) →
    MachineDefines mctx mref cctx cref p.decl p.d.shape →
    MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D →
    (∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k) →   -- CASE RESTRICTION
    Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc →
    ∀ n, TopShips p (n + 1) p.decl b raw D ∧ ChildShips p (n + 1) b D
```
- Relation to `StepStmt` (Defs:300-313): same telescope plus case premises and data (as `MemParentStmt'`); decoding strengthened to
  `CallDec` only; `∀ n` gives `∃ n` at `n + 1 := 1`.
- **Marked:** `hnomem` (the `instTagged` row) and the strengthened decoding are a CASE RESTRICTION; coverage of `StepStmt`'s one-output
  case is UNSATISFIED until §7 resolves. `OneOutStepStmt` is NOT a proved statement: its first conjunct is stage B (blocked).

## 5. S4-WID — the per-call width relation (separate from `CallDec`)
**What is needed.** `RunFacts.wid : instOutWidthsOk (childMap D.modules) (declWidth b) b.body = true` (Tools/ShippingHierOpen.lean:503-514):
for each instance and child output `outP`, the connected wire `outW` has `declWidth b outW = outP.ty.bitWidth`. On the one-output
closing `outW = names[machNIn + k]` (CallStmt, Inst:192), the port of the call-result BINDER at index `p.kD + k`
(`binders = bsIn ++ slotBs ++ letBs`, Auto:212-214; `callsOk p.kD` gives `p.kD + insts.length = nIn`, Tools/ShippingCallsShape.lean:107;
hence `p.d.shape.binders[p.kD + k]? = (p.d.bsIn.drop p.kD)[k]?` for `k < insts.length`). `closingNDecl p.d.shape`
(Tools/ShippingCallWidthsEntry.lean:62; the closing's `nDecl`, Elab:5216) equals `p.kD` under `ok` + `callsOk p.kD` + slot count
(arithmetic; small missing lemma `closingNDecl_eq_kD`).

**The relation** (new, in `Tools/ShippingGen2OneOut.lean`; NOT a conjunct of `CallDec`, NOT added to `StepStmt` or `DataOk`):
```lean
/-- The binder of call `k`'s result has the bit width of the callee package's ONLY layout output (the unique output, not a field
name). `kindTy`: Tools/ShippingMachineEntry.lean:232. -/
def OneOutWidth (P : Pkgs ι dom) (p : Pkg ι dom) (k : Nat) : Prop :=
  ∀ (hk : k < p.d.shape.insts.length) (q : Pkg ι dom), P (p.d.shape.insts[k]).1 = some q →
    ∀ o : OutField, q.d.shape.layout.outs = [o] →
      (p.d.shape.binders[p.kD + k]?).map (fun bn => (kindTy bn.2).bitWidth) = some o.ty.bitWidth
```
`o.ty.bitWidth`, not `o.width`: `instOutWidthsOk` reads the port type, and `CombChildRunN`'s first conjunct (Defs:63) makes the
served module's output `{ name := o.name, ty := o.ty }`.

**Why existing rows do not supply it.**
- `callWidthsOk` (Tools/ShippingCallWidths.lean:51-56) compares only outputs named `instFields.getD k ""`; with `instFields = []` that is
  `""`, and the condition is VACUOUS (finding A, Tools/ShippingCallWidthsStrict.lean:3-10).
- `callWidthsStrict` (CallWidthsStrict.lean:37-42) is the non-vacuous form (`instFields[k]? = none` → every output compared), with a
  caller-chosen `kidOuts`. `∀ k, OneOutWidth P p k` follows from it at `nDecl := p.kD` and
  `kidOuts k := match P ((p.d.shape.insts.map (·.1))[k]?.getD .anonymous) with | some q => q.d.shape.layout.outs | none => []`
  (bridge lemma `oneOutWidth_of_strict`, missing, small).
- `callArgsOk` / `callArgsOkAt` (Tools/ShippingPortsMatchRaw.lean:199; Tools/ShippingGen2Adapt.lean:73) are the ARGUMENT widths
  (binder of `args[j]` vs callee port width), not the result.

**Supplier survey.**
| source | gives | status |
|---|---|---|
| real data, `callerL → pickByteH` | `callerL_strict : callWidthsStrict callerL.machineData 1 (fun _ => pickByteH.machineData.shape.layout.outs) = true` (Tests/Compiler/OneOutCallerLTest.lean:275-278, `decide`) | imported by Tests/AllTests.lean:176; ONE pair; needs `P ``pickByteH = some q` with `q.d = pickByteH.machineData` and callerL's `p.kD = 1` |
| real data, from reader links | `callWidthsStrict_of_linksFH*` (Tools/ShippingCallWidthsEntryFH.lean:64; Tools/ShippingCallWidthsEntryFR1.lean:128-151) | Tests/Compiler/CallWidthsEntryExampleTest.lean:16-46 lists `NIN` and `ResC` as supplied by nothing; that file says "UNVERIFIED: written, not built" |
| generator | parent template emits `callWidthsOk … (fun _ => @C@.machineData.shape.layout.outs)` (Tools/ShippingSeqParentGenD2.lean:262) | the VACUOUS row for `instFields = []`; no generator emits `callWidthsStrict` or `OneOutWidth` |
| the closing | `instStmt` / `closeInsts` (Machine.lean:272-292, 396-427) | NO width check |
| the elaborator | the call's result kind `res` (`machInstance`, Elab:4049-4058; `.bits _` only on this route) is the callee's result type | a source typing fact; no kernel statement links it to `q.d.shape.layout.outs` (the `ResC` gap) |

**Coverage obligation G-ONEOUT-WID** (recorded, not added silently): for every package `p` on the one-output route,
`∀ k, OneOutWidth P p k`, derived from data (`callWidthsStrict` per declaration, as `callerL_strict`) or from the reader/elaborator
(`ResC`). Until then `hW` is a named premise of stage B.

**Use (missing lemma `core_instOutWidthsOk_oneA`).** From `hW`; `MachineWired`'s second one-output clause (Entry:667-669: every
instance of the body is a `CallStmt` of some `k`); the served module's output equation (stage A's `CombChildRunN`, via `Served1P` +
`ShipsRes`); and `declWidth b outW = (kindTy bn.2).bitWidth` (as `declWidth_of_unique` at ParentRunFactsA:557-560), conclude
`instOutWidthsOk (childMap D.modules) (declWidth b) b.body = true`. Alternative child side: `ChildOutTys` of a `RealChildA` result,
as in `hkidW_strict` (CallWidthsStrict.lean:84-93).

## 6. S4-BD — risk-check plan for `KSBoundedIn` of comb children
**What is needed.** Consumer 1's `hBd` (Srm33Core:29) is used ONCE: `have hKSb := hBd b D hBdb` (Srm33Core:124), feeding `fitX_of_run`
(Tools/ShippingHierOptRun.lean:668) at Srm33Core:176. The only supplier, `KSn_boundedIn` (Tools/ShippingMachineShipsDepth.lean:171),
needs `kidsMaskedN` (ShipsDepth:163-168) = every instance's module satisfies `outsMaskedN` (ShipsDepth:155-160): each output assigned
once by a `selfMasked` expression (`.const` / `.slice` only, Tools/ShippingMachineShipsHier.lean:578-581) no wider than the port, no memory.

**Risk checks (evaluations to run; none were run for this document):**
1. `outsMaskedN` / `kidsMaskedN` on REAL served children — the module `moduleByName D.modules` returns in a real parent run, after the
   full entry's post-processing: (a) `pickByteH` served to `callerL` (Tests/Compiler/ShippingMachineLinkedTest.lean:21, :32);
   (b) the gate leaf `pick` served to `caller` (Tests/Compiler/ShippingMachineInstTest.lean:29). Not on hand-built modules.
2. A minimal assign-only child that returns an input unchanged (e.g. `idH (x : Signal defaultDomain (BitVec 8)) := x`), compiled by the
   real entry and called by a one-output parent; `outsMaskedN` on the served module. Record what the real entry emits; do not assume
   `out := ref x`.
3. Interpretation: `kidsMaskedN = false` does NOT refute `KSBoundedIn` (sufficient, not necessary). `KSBoundedIn` (HierOptRun:658-663)
   quantifies over EVERY `env`, so a child whose output is an unmasked input read may violate it — a fact about the predicate on that
   module. A handwritten module or example is NOT a counterexample of a successful compilation; only a module served in a successful
   real run counts.

**If syntactic masking cannot be supplied across real routes — preferred design (not realised):** a RUN-LOCAL range-propagating
consumer (input fit + child meaning ⇒ output fit, on the run), in a COPY of consumer 1 that replaces the `hKSb` use at Srm33Core:124/:176
by a run-local fit lemma and drops `Bd`/`hBd`/`Inv`/`hRI` (Srm33Core:27-30). Needed suppliers:
- input fit: TopShips' antecedents `ins t x < 2 ^ declWidth b x` and the `st0` fit (Defs:287-290);
- input width correspondence: `callArgsOkAt p.d p.kD k q.portWidths` (Adapt.lean:73, `Pkg.portWidths` :80) — argument wires have the
  callee's port widths;
- per-step fit: the let wires carry the source lets on the run (trace's let clause, TraceX:409-411), `< 2 ^ l.1.width` (`Pkg.lsrc_hl`,
  Pkg.lean:102-105);
- source output range: either `∀ v, InRange v q.ports → ∀ f, (q.S i (fun _ => v))[0]? = some f → f 0 < 2 ^ o.width` — NO existing lemma
  (`Pkg.src_length` / `Pkg.src_get`, CombKid:56/:79, give shape only) — or, on the parent's run, `CallDec`'s equation
  `posEnc (p.extBS …) (p.extS …) (p.kD + k) kind = f τ` with a bound lemma for `posEnc` at a `.bits w` kind (Entry:293; missing) plus
  §5's `OneOutWidth`.
No compiler mask, no FG premise, no change to `KSBoundedIn`.

## 7. S4-MEM — case restriction and the independent probe
**Intermediate case (§4).** `OneOutStepStmt` is ordinary-only: `hnomem` (both halves) and the strengthened `hdec` are a case
restriction; `StepStmt`'s one-output coverage stays unsatisfied.

**Probe P-MEM (independent; one question, on the same run): does a SUCCESSFUL one-output closing exclude memory-origin entries?**
Follow one run: origin → `synth c` → served result → `instStmt`.
- Origin: a memory call is read by `machInstance … (.mem combo aw dw)` followed by `instStruct := true` (Elab:3956-3960); every entry
  pushes a field name (Elab:4080); the shape takes `instFields := if st.instStruct then st.instFields.toList else []` (Elab:5196). So,
  BY THE SOURCE TEXT, a reader-produced shape with `instFields = []` has no `.mem` entry (nor `.field`, Elab:4125, nor a Bool result,
  Elab:4058).
- Closing: `instFields.isEmpty` selects `closeInstsM` (Elab:5261-5262), which calls `synth c` for EVERY entry regardless of origin
  (Elab:5211); `closeInstsGM` is origin-aware (Elab:5235-5238). So the closing itself does NOT exclude a memory origin; the exclusion,
  if any, is the reader's.
- Served result / `instStmt`: a `.mem` entry on this path would be served by `synth` of the placeholder name (a declaration may carry
  it, Sparkle/Compiler/MachInstOrigin.lean:5-12), not by `memModule`; `instStmt`'s clk refusal (Machine.lean:278) applies to THAT result.
- **If yes** (the reader excludes): prove it from the run — `MachineDefines` (the shape is the reader's output) ⇒ `instFields = [] →
  ∀ k, (instOrigins.getD k .ord).child? = none`. The reader (`machInstance`, Elab:4049) is `partial`, so this needs a reader invariant:
  on the fuel-total candidate `machineShapeF` (not switched), or per declaration as the decided origin half of `hnomem`. Then the small
  lemma below removes `MemDec` without `Nonempty ι`.
- **If no** (a shape with `instFields = []` and a `.mem` origin is produced): a route-aware decoding/`Reach` and a memory-meaning
  consumer are needed — the SAME obligation as M3 G-ONEOUT-REACH (sync with M3; not solved here).

**Small lemma (candidate, provable):**
```lean
theorem memDec_vacuous_of_ord {p : Pkg ι dom} {k : Nat} {c : Name}
    (hord : (p.d.shape.instOrigins.getD k .ord).child? = none) (hm : MemDec p k c) : ∀ i : ι, False
  -- MemFacts' first conjunct (Tools/ShippingMachineCallsLinkedT.lean:37-38) is `child? = some (memModule cb aw dw)`
```
With `hord` for every `k`, `StepStmt`'s `MemDec p k _ ∨ ∃ q, … CallDec p q k` gives per `k`: `CallDec`, or `∀ i : ι, False`; on the
latter branch every `∀ i` conclusion (`ComposedHB`'s, `ChildShips`') is vacuous. That avoids `Nonempty ι`, but it needs a consumer
variant taking the per-`k` disjunction, and `hord` has a supplier only from the probe (or from `hnomem`).

**Cautions (recorded):**
- `MemDec` (Defs:116-118) carries the origin INSIDE `∀ i`: for empty `ι` it holds vacuously and yields no origin.
- Refuting `Served1P`'s left disjunct (`mc = memModule …`, which has a `"clk"` input, Sparkle/Compiler/MachMemory.lean:52-56) by
  `callStmt_noClk` negates NEITHER the parent's origin NOR `MemDec`.
- No permanent `Nonempty ι` premise anywhere.
- `hnomem`'s NAME half (`memChild? x.1 = none`, MachMemory.lean:65-70) is not implied by the origin; it is an additional restriction
  (it excludes ordinary calls of a declaration carrying a placeholder name).

## 8. Integration note
- `Served1P (ShipsRes L P)` is a premise everywhere (G-SERVED, `ServedShipsStmt`, Defs:251, not built).
- At the combined SHA with M3's `InstClosed`, RE-VERIFY the `ShipsRes` projections used here (`.1 : RealChildA L.O c r`,
  `.2 : ∃ q n, P c = some q ∧ q.decl = c ∧ ChildShips q n r.1 r.2`, Defs:135-136) and every consumer of them —
  `machine_linked_callsServed1`, `machine_linkedT_callsServed` (Tools/ShippingGen2Consumer.lean:30), the `memParent_*` theorems —
  against the combined definitions; a check made at another SHA is not reused.

## 9. Missing vs existing; stop conditions
**Existing (cited):** `childFn_of_combRun`, `combS_pointwise` (CombKid:174, :205); `OneOutCall`, `oneOutCall_of_callDec` (CallField:164,
:177); C1-C3 (AComb); `CallStmt`, `instStmt_some`, `closeInsts_calls` (Inst:190, 205, 247); `closeInsts_kidsComb`, `closeInsts_acyclic`
(ChildServe:248, 200); `core_closeInstsA`, `core_runFactsHA` (ParentDesignA:152, 494); `composedNWn_of_H`, `kidsComb_of_B` (DepthHR:208,
31); consumer 1 (Srm33Core:24); `seqChildRunN_of_composedNW_run` (C6:28); `MemParentDataOk.rows`, `data_h*` (MemData:16-66);
`callWidthsStrict` (CallWidthsStrict:37); `callerL_strict` (OneOutCallerLTest:275).

**Missing, provable from existing facts (stage A only):** `callStmt_noClk`, `combChildRunN_of_noClk`, `kidsCombB_assign`, `data_hI`;
`ComposedHB` + `composedHB_id`, `machine_linked_ofB` + `machine_linked_of_viaB`, `composedNWn_of_HB` + check 3; `oneP`, `oneF`,
`machine_linked_callsServed1`; `oneOut_composedNW`, `oneOut_childShips` — under the residues of stage A (§3). Also small and
independent: `closingNDecl_eq_kD`, `oneOutWidth_of_strict`, `memDec_vacuous_of_ord`.

**No supply route or proof AT PRESENT (removed from rev1's list; not a claim of underivability):** `oneOut_topShips` without `hW`/`hBd` (stage B; also needs the new
`core_instOutWidthsOk_oneA`), `oneOut_step : OneOutStepStmt L P DataOk` (needs stage B), and `StepStmt` coverage (stage C).

**Stop conditions (a needed fact with no supplier; reported, not added silently):**
- **S4-WID:** `∀ k, OneOutWidth P p k` (§5); coverage obligation G-ONEOUT-WID; the generator emits only the vacuous row.
- **S4-BD:** `KSBoundedIn … (KSn …) b.body _` for served comb children (§6); run the risk checks; if masking fails on real routes,
  decide on the run-local consumer.
- **S4-MEM:** the origin fact for `instFields = []` (§7, probe P-MEM); until then `hnomem` + strengthened `hdec` are a case restriction
  and stage C is open; a "no" answer merges into M3 G-ONEOUT-REACH.
- **G-SERVED:** `h` (all stages).
- Checks 1-3 (§2) failing to elaborate as written (e.g. `rfl` for `composedHB_id`) are reported, not patched over.

## 10. Not claimed
- Nothing here is built or proved. No `TopShips`/`ChildShips` for slotless one-output parents (S5).
- S4-WID, S4-BD, S4-MEM are not resolved; the evaluations of §6 and the probe of §7 were not run.
- Line numbers are at ee4f03b1.
