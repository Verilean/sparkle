import Tools.ShippingGen2SlotlessTop
import Tools.ShippingGen2TopVacuity
import Tools.ShippingSlotlessClk
import Tools.ShippingSlotlessKidFacts
import Tests.Gen3.ExpectedType
set_option autoImplicit false
-- NOT BUILT after the U-TOP-DEF switch (Defs `TopShips` is R-G; previous builds g2nc3-ba4334f8 / g2nc4-36342cb8 were against the OLD `TopShips`).
-- U-TOP-DEF edits: `TopShipsRG` (local copy) is now Defs `TopShips`; the old text is `TopShipsOld`; L1/L2 live in TopContract.
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # Checks for the NC suppliers, L1-L4 and S5 stage C (S5_SLOTLESS_FREEZE.md rev1 §5, §7, §8 + rev1.1;
TOP_CONTRACT_REVISION.md §3 + rev1.1)

1. **Expected types** (`Tests.Gen3.ExpectedType.checkExpected`: binder by binder, names, binder infos, types,
   conclusion) against independent `Exp…` statements written from the freeze telescopes: C2 `TopShipsNC` (definition
   value), the R-G `TopShips` of Defs (definition value; U-TOP-DEF), the frozen old text `TopShipsOld` (definition value), L1-L4,
   `topShipsOld_of_NC`, U-TOP-S2 (pure and run
   level), C1, C3's projection, the `outNameOk` supplier, C4, C5a. Meaning-changing MUTANTS must be REJECTED.
2. **Audit, full reachable closure** (`ncReach`, as `s5Reach`/`s3Reach`: type and explicit body of every reached
   constant): C4, C5a and the U-TOP-S2 producers do not reach `TopShips` (R-G), the old text `TopShipsOld`, L1-L3
   (`topShips_toOld`, `topShips_ofOld`, `topShips_of_NC`) or `topShipsOld_of_NC`. Detector controls with the SAME search: a direct
   use of `TopShips`, a use through two helpers in other namespaces, a direct use of `topShips_of_NC`, a direct use of
   `TopShipsOld` are found; an unrelated theorem is not.
3. **P3-core** (rev1.1 note 1: an execution control of A2 ONLY; it does not check `SourceInputs`, the outer
   ids/cache/regs witness, C4 or C5a): a concrete clock-free module `m0` (input `a`, an instance of the comb child
   `c0 : y := i` reading `a` into `x`, `o := x`) in the design `d0`, at depth 1, `T = 2`, `ins t "a" = (t+3) % 256`,
   zero state. (i) the inner premises of `TopShipsNC` that do not mention the package witnesses hold at `m0`
   (passthrough over `regs = []`, slot inits over `slots = []`, `ResetNk 1 m0 d0 kids0`, input fit, state fit);
   (ii) `NoTouchZ ["rst","clk"] m0.body` is proved, the run at `slSeedZ` is computed, A2 gives the run at `seedIn`, and
   its conclusion yields the outputs `[4, 3]` at `"o"`, cross-checked by direct evaluation of the `seedIn` run;
   (iii) the OLD clk binder (Defs:283) is refuted at `m0`, while every premise in (i) holds.
4. Axioms: `checkAxioms` and `#print axioms`.
5. **PAIR checks against the ORIGINAL declarations** (§2b; S5 freeze §8 item 1; `s5CheckPair`, S5Check:380-413,
   extended by deletions and by a second level inside the conclusion): C1 vs `hierRefineCheck_linked`
   (HierOptRun:532-655), C2 vs `TopShips` (definition values; only the rst and clk premises deleted), C4 vs
   `machine_ships_hierC_run` (FitChain:1073-1232, namespace `Tools.ShippingSrm33`), C5a vs `oneOut_topShipsO`
   (OneOutTopO:334-415), U-TOP-S2 pure vs `slotlessLeaf_topShips_of_LB` (SlotlessLeaf:180-191). Exactly the binder
   changes the freeze lists are allowed; anything else fails. U-TOP-S2 run level vs `slotlessLeaf_ships`
   (SlotlessLeaf:425-448) by a binder CORRESPONDENCE TABLE (§2b, in the comment there).
6. **Second closure audit** (§2c; S5 freeze §8 item 2, as `s5Reach`): C1, C4, C5a and the U-TOP-S2 producers do not
   reach `Tools.ShippingSlotlessClk.SeqKid`, any `Tools.ShippingSlotlessClk.*` or any
   `Tools.ShippingSlotlessKidFacts.*` constant. Same BFS; detector controls: direct `SeqKid`, `SeqKid` through two
   helpers in other namespaces, direct `core_runFactsS` found; an unrelated theorem not found. -/

/-! ## 0. Detector fixtures for the closure audit -/
namespace Tests.Gen2.TopNCReachHelperA
/-- helper 1 (uses `TopShips`) -/
theorem helperA : True := (fun _ => trivial) @Tools.ShippingGen2.TopShips
end Tests.Gen2.TopNCReachHelperA

namespace Tests.Gen2.TopNCReachHelperB
/-- helper 2 (uses helper 1) -/
theorem helperB : True := Tests.Gen2.TopNCReachHelperA.helperA
end Tests.Gen2.TopNCReachHelperB

namespace Tests.Gen2.TopNCReachFixture
/-- closure-detector control: direct use of `TopShips` -/
theorem badDirect : True := (fun _ => trivial) @Tools.ShippingGen2.TopShips
/-- closure-detector control: use through two helpers in other namespaces -/
theorem badIndirect : True := Tests.Gen2.TopNCReachHelperB.helperB
/-- closure-detector control: direct use of `topShips_of_NC` -/
theorem badNC : True := (fun _ => trivial) @Tools.ShippingGen2.topShips_of_NC
/-- closure-detector control: direct use of the old text `TopShipsOld` -/
theorem badOld : True := (fun _ => trivial) @Tools.ShippingGen2.TopShipsOld
/-- closure-detector control: unrelated (must NOT be flagged) -/
theorem goodUnrelated : True := trivial
end Tests.Gen2.TopNCReachFixture

/-! Fixtures of the SECOND audit (old-boundary slotless facts; as S5Check's `S5ReachFixture`) -/
namespace Tests.Gen2.TopNCSlReachHelperA
/-- helper 1 (uses `SeqKid`) -/
theorem helperA : True := (fun _ => trivial) @Tools.ShippingSlotlessClk.SeqKid
end Tests.Gen2.TopNCSlReachHelperA

namespace Tests.Gen2.TopNCSlReachHelperB
/-- helper 2 (uses helper 1) -/
theorem helperB : True := Tests.Gen2.TopNCSlReachHelperA.helperA
end Tests.Gen2.TopNCSlReachHelperB

namespace Tests.Gen2.TopNCSlReachFixture
/-- second-audit control: direct use of `SeqKid` -/
theorem badDirect : True := (fun _ => trivial) @Tools.ShippingSlotlessClk.SeqKid
/-- second-audit control: use of `SeqKid` through two helpers in other namespaces -/
theorem badIndirect : True := Tests.Gen2.TopNCSlReachHelperB.helperB
/-- second-audit control: direct use of a `SlotlessKidFacts` theorem -/
theorem badKidFacts : True := (fun _ => trivial) @Tools.ShippingSlotlessKidFacts.core_runFactsS
/-- second-audit control: unrelated (must NOT be flagged) -/
theorem goodUnrelated : True := trivial
end Tests.Gen2.TopNCSlReachFixture

namespace Tests.Gen2.TopNCCheck

/-! ## 1. Expected statements -/

section ExpContracts
-- the opens of Tools/ShippingGen2TopNC.lean §1 (= Tools/ShippingGen2Defs.lean)
open Lean hiding Module
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
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
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingGen2 (Pkg TopShips TopShipsOld TopShipsNC)

/-- C2 (S5 freeze §5): Defs:273-295 with line :283 deleted. -/
def ExpTopShipsNC {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- MUTANT of C2: the reset premise kept (only the clock deleted). -/
def MutTopShipsNCrst {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      (∀ t, ins t "rst" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- R-G (TOP_CONTRACT_REVISION §2): the line holding the rst and clk premises replaced by the two guarded premises
(U-TOP-DEF: this is now the text of Defs `TopShips`). -/
def ExpTopShipsRG {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      ("rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0) →
      ("clk" ∈ b.inputs.map (·.name) → ∀ t, ins t "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- The PRE-R-G text (history pin): the unguarded rst premise and the `seedIn … "clk"` premise. -/
def ExpTopShipsOld {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      (∀ t, ins t "rst" = 0) → (∀ t st, seedIn b ins t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- MUTANT of R-G: the clock premise unguarded (the old Defs:283 clk binder). -/
def MutTopShipsRGclk {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design) : Prop :=
  ∃ ids : List FVarId, ids.Nodup ∧ ids.length = p.d.shape.binders.length ∧
  ∃ (cache : IO.Ref (ExprStructMap String)) (regs : List String),
    regs.Nodup ∧ regs.length = p.d.ss.length ∧
    ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
      (T : Nat) (ins : Nat → String → Nat) (st0 : String → Nat) (mems : MEnv) (kids : String → KT n),
      (∀ t st, t < T → SourceInputs declName (p.d.bsIn.take p.kD) ids cache
        (fun j => (p.extBS i bools bits j).val (T - 1 - t))
        (fun j n => (p.extS i bools bits j n).val (T - 1 - t)) (seedIn b ins t st)) →
      (∀ t st r, r ∈ regs → seedIn b ins t st r = st r) →
      ("rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0) →
      (∀ t st, seedIn b ins t st "clk" = 0) →
      (∀ (k : Nat) (r : String) (f : SlotField), regs[k]? = some r →
        p.d.shape.layout.slots[k]? = some f → st0 r = f.init) →
      ResetNk n raw D kids →
      (∀ t x, x ∈ b.inputs.map (·.name) → ins t x < 2 ^ declWidth b x) →
      (∀ x ∈ (openIns b).map (·.name), x ∉ bodyInstOuts (childMap D.modules) b.body →
        st0 x < 2 ^ declWidth b x) →
      ∃ envsO, runModuleTG (KSn (childMap D.modules) n) (declWidth (checkedOptimize b))
          (childMap D.modules) (checkedOptimize b).body (seedIn b ins) T ⟨st0, mems, kids⟩ = some envsO ∧
        envsO.length = T ∧
        ∀ j (hj : j < envsO.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          p.d.shape.layout.outs[k]? = some o → (p.src i bools bits)[k]? = some f → (envsO[j]'hj) o.name = f j

/-- L1 `topShips_toOld`: new ⇒ old, no hypothesis. -/
def ExpL1 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design),
    TopShips p n declName b raw D → TopShipsOld p n declName b raw D

/-- L2 `topShips_ofOld`: old ⇒ new, given both inputs. -/
def ExpL2 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design)
    (hr : "rst" ∈ b.inputs.map (·.name)) (hc : "clk" ∈ b.inputs.map (·.name)),
    TopShipsOld p n declName b raw D → TopShips p n declName b raw D

/-- MUTANT of L2: without the clock membership (old ⇒ new for clock-free modules is NOT claimed). -/
def MutL2noClk : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design)
    (hr : "rst" ∈ b.inputs.map (·.name)),
    TopShipsOld p n declName b raw D → TopShips p n declName b raw D

/-- L3 `topShips_of_NC`: NC ⇒ new, no hypothesis. -/
def ExpL3 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design),
    TopShipsNC p n declName b raw D → TopShips p n declName b raw D

/-- L4 `topShipsNC_of_topShips`: new ⇒ NC, given neither input. -/
def ExpL4 : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design)
    (hr : "rst" ∉ b.inputs.map (·.name)) (hc : "clk" ∉ b.inputs.map (·.name)),
    TopShips p n declName b raw D → TopShipsNC p n declName b raw D

/-- MUTANT of L4: only the clock absent (rev1.1 note 3: "no clk" alone is not claimed sufficient). -/
def MutL4noRst : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design)
    (hc : "clk" ∉ b.inputs.map (·.name)),
    TopShips p n declName b raw D → TopShipsNC p n declName b raw D

/-- The earlier `topShips_of_NC` (NC ⇒ old text), now `topShipsOld_of_NC`. -/
def ExpTopShipsOldOfNC : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (declName : Name)
    (b raw : Sparkle.IR.AST.Module) (D : Design),
    TopShipsNC p n declName b raw D → TopShipsOld p n declName b raw D

end ExpContracts

section ExpS2
-- the opens of Tools/ShippingGen2TopNC.lean §2 (= Tools/ShippingGen2SlotlessLeaf.lean)
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (dv)
open Tools.ShippingGen2 (Pkg Laws LeafDataOk MachineTaken TopShipsNC TopShips)

/-- U-TOP-S2, pure: `slotlessLeaf_topShips_of_LB`'s binders + `hinA`, conclusion `TopShipsNC`. -/
def ExpS2LB : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) {raw b : Module} {D : Design}
    (hL : MachineTraceLB p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hok : p.d.ok = true) (hSS : p.d.ss.length = p.d.shape.layout.slots.length)
    (houtTy : ∀ o ∈ p.d.shape.layout.outs, o.ty.bitWidth = o.width)
    (htake : p.d.bsIn.take p.kD = p.d.bsIn)
    (hclosed0 : readsClosedB ((Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).inputs.map (·.name))
        (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body = true ∧
      (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw).body.all isAssign = true)
    (hinA : ∀ q ∈ raw.inputs, Sparkle.IR.NameHints.Allocated q.name)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw)) (n : Nat),
    TopShipsNC p n p.decl b raw D

/-- U-TOP-S2, run level. -/
def ExpS2Run : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module}
    {D : Design}
    (hdata : LeafDataOk p) (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D) (n : Nat),
    TopShipsNC p n p.decl b raw D

/-- MUTANT of U-TOP-S2 (run level): conclusion R-G `TopShips` in place of `TopShipsNC`. -/
def MutS2RunRG : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module}
    {D : Design}
    (hdata : LeafDataOk p) (hnoI : p.d.shape.insts = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D) (n : Nat),
    TopShips p n p.decl b raw D

end ExpS2

section ExpC
-- the opens of Tools/ShippingGen2SlotlessTop.lean §C1-C4 (= FitChain Block C)
open Tools.ShippingShipsDesignSV Tools.ShippingMachineShipsHier Tools.ShippingMachineShipsDepth
open Lean hiding Module Expr
open Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
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
open Tools.ShippingGen2SlotlessParent (NoTouchZ)
open Tools.ShippingGen2SlotlessTop (RunFactsNR)

/-- C1 (S5 freeze §5). -/
def ExpC1 : Prop :=
  ∀ {σ : Type} (KS : KStep σ) (hloc : KSLocal KS)
    (children : String → Option (Module × WEnv)) {m o : Module}
    (hchk : Sparkle.IR.RefineCheck.hierRefineCheck m o = true)
    (hwfM : linkedWF children m.body = true) (hwfO : linkedWF children o.body = true)
    (hndM : (instNames m.body).Nodup) (hndO : (instNames o.body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hOutM : ∀ w ∈ bodyInstOuts children m.body, w ∈ (openIns m).map (·.name))
    (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs)
    (hfitX : ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x)
    (hnoR : Sparkle.IR.OptCheck.seqRegs m = []),
    o.inputs = m.inputs ∧ o.outputs = m.outputs ∧
    ∃ envsO, runModuleTG KS (declWidth o) children o.body (seedIn m ins) T s = some envsO ∧
      envsO.length = envs.length ∧
      ∀ p ∈ m.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name

/-- MUTANT of C1: `hnoR` dropped (the reset-free transfer needs a register-free module). -/
def MutC1noR : Prop :=
  ∀ {σ : Type} (KS : KStep σ) (hloc : KSLocal KS)
    (children : String → Option (Module × WEnv)) {m o : Module}
    (hchk : Sparkle.IR.RefineCheck.hierRefineCheck m o = true)
    (hwfM : linkedWF children m.body = true) (hwfO : linkedWF children o.body = true)
    (hndM : (instNames m.body).Nodup) (hndO : (instNames o.body).Nodup)
    (hnofb : ∀ mn iname conns, Stmt.inst mn iname conns ∈ o.body → ∀ child cwe,
      children mn = some (child, cwe) → ∀ c ∈ inConns child.outputs conns, ∀ w,
        c.2 = .ref w → w ∉ instOutWires child.outputs conns)
    (hOutM : ∀ w ∈ bodyInstOuts children m.body, w ∈ (openIns m).map (·.name))
    (ins : Nat → String → Nat)
    (hinsFit : ∀ t x, x ∈ m.inputs.map (·.name) → ins t x < 2 ^ declWidth m x)
    {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth m) children m.body (seedIn m ins) T s = some envs)
    (hfitX : ∀ j (hj : j < envs.length), ∀ x ∈ (openIns m).map (·.name),
      (envs[j]'hj) x < 2 ^ declWidth m x),
    o.inputs = m.inputs ∧ o.outputs = m.outputs ∧
    ∃ envsO, runModuleTG KS (declWidth o) children o.body (seedIn m ins) T s = some envsO ∧
      envsO.length = envs.length ∧
      ∀ p ∈ m.outputs, ∀ j (hj : j < envsO.length) (hj' : j < envs.length),
        (envsO[j]'hj) p.name = (envs[j]'hj') p.name

/-- C3's projection. -/
def ExpC3toNR : Prop :=
  ∀ {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {b : Sparkle.IR.AST.Module}
    (h : Tools.ShippingGuardsSound.RunFacts C b), RunFactsNR C b

/-- C3's fields: `RunFacts`'s without `rst` (each field's type pinned). -/
example {C : String → Option (Sparkle.IR.AST.Module × WEnv)} {b : Sparkle.IR.AST.Module} (h : RunFactsNR C b) :
    Sparkle.IR.RefineCheck.hierGate b = true ∧ Tools.ShippingHierOpen.linkedWF C b.body = true ∧
    (Tools.ShippingHierState.instNames b.body).Nodup ∧
    Tools.ShippingHierPremisesBase.noSelfRead C b.body = true ∧
    Tools.ShippingHierPremisesBase.outsExtracted C b = true ∧
    Tools.ShippingHierOpen.instOutWidthsOk C (Sparkle.IR.RegDedup.declWidth b) b.body = true :=
  ⟨h.gate, h.wfB, h.ndB, h.self, h.outs, h.wid⟩

/-- The `outNameOk` supplier (rev1.1 note 2), with its full type. -/
def ExpOutNameOk : Prop :=
  ∀ {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
    {declName : Name} {shape : Sparkle.Compiler.Elab.MachineShape} {raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w (raw, D) w1)
    (entry : MachineDefines mctx mref cctx cref declName shape),
    ∀ o ∈ shape.layout.outs, outNameOk o.name = true

/-- C4 (S5 freeze §5). -/
def ExpC4 : Prop :=
  ∀ {n : Nat} (hloc : ∀ D : Design, KSLocal (KSn (childMap D.modules) n))
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
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hsl0 : d.shape.layout.slots = [])
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : C mctx mref cctx cref)
    (facts : Bnd mctx mref cctx cref w raw D → RunFactsNR (childMap D.modules) b)
    (hnR : "rst" ∉ raw.inputs.map (·.name))
    (hnC : "clk" ∉ raw.inputs.map (·.name))
    (hZ : NoTouchZ ["rst", "clk"] raw.body),
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

/-- MUTANT of C4: `hZ` dropped (the syntactic premise B1 supplies; without it A2 does not apply). -/
def MutC4noZ : Prop :=
  ∀ {n : Nat} (hloc : ∀ D : Design, KSLocal (KSn (childMap D.modules) n))
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
    (hslots : d.ss.length = d.shape.layout.slots.length)
    (hsl0 : d.shape.layout.slots = [])
    {mctx : Meta.Context} {mref : ST.Ref IO.RealWorld Meta.State}
    {cctx : Core.Context} {cref : ST.Ref IO.RealWorld Core.State} {w w1 : Void IO.RealWorld}
    {b raw : Sparkle.IR.AST.Module} {D : Design}
    (hcore : RunsTo (synthesizeCombinationalCore declName [] false) mctx mref cctx cref w
      (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref declName d.shape)
    (closes : C mctx mref cctx cref)
    (facts : Bnd mctx mref cctx cref w raw D → RunFactsNR (childMap D.modules) b)
    (hnR : "rst" ∉ raw.inputs.map (·.name))
    (hnC : "clk" ∉ raw.inputs.map (·.name)),
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

end ExpC

section ExpC5a
-- the opens of Tools/ShippingGen2SlotlessTop.lean §C5a (= OneOutTopO:255-278)
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.RefineCheck (mergeChecked)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingEntrySoundness Tools.ShippingMachineEntry
open Tools.ShippingChildInvA (AdmCtx)
open Tools.ShippingChildBndCore (dv)
open Tools.ShippingGen2 (Pkg Pkgs Laws MemParentDataOk MachineTaken CallDec ServedP ShipsRes OneOutWidth
  TopShips TopShipsOld TopShipsNC)

/-- C5a (S5 freeze §5): `oneOut_topShipsO`'s binders, `hsl` → `hsl0`, `hrst` added, conclusion `TopShipsNC`. -/
def ExpC5a : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module}
    {D : Design}
    (hdata : MemParentDataOk p)
    (hord : ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
      (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hW : ∀ k, OneOutWidth P p k)
    (hrst : "rst" ∉ raw.inputs.map (·.name))
    (n : Nat),
    TopShipsNC p (n + 1) p.decl b raw D

/-- MUTANT of C5a: conclusion the OLD text `TopShipsOld` (vacuous in its inner part for case C). -/
def MutC5aOld : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module}
    {D : Design}
    (hdata : MemParentDataOk p)
    (hord : ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
      (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hW : ∀ k, OneOutWidth P p k)
    (hrst : "rst" ∉ raw.inputs.map (·.name))
    (n : Nat),
    TopShipsOld p (n + 1) p.decl b raw D

/-- MUTANT of C5a: the case binder `hrst` dropped (case S has clock/reset inputs). -/
def MutC5aNoRst : Prop :=
  ∀ {ι : Type} {dom : ι → DomainConfig}
    {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module}
    {D : Design}
    (hdata : MemParentDataOk p)
    (hord : ∀ (k : Nat) (hk : k < p.d.shape.insts.length),
      (p.d.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl0 : p.d.shape.layout.slots = [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hW : ∀ k, OneOutWidth P p k)
    (n : Nat),
    TopShipsNC p (n + 1) p.decl b raw D

end ExpC5a

open Lean Meta Tests.Gen3.ExpectedType

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- definitions (values) and theorems (types)
  checkExpected ``Tools.ShippingGen2.TopShipsNC ``ExpTopShipsNC
  checkExpected ``Tools.ShippingGen2.TopShips ``ExpTopShipsRG
  checkExpected ``Tools.ShippingGen2.TopShipsOld ``ExpTopShipsOld
  checkExpected ``Tools.ShippingGen2.topShips_toOld ``ExpL1
  checkExpected ``Tools.ShippingGen2.topShips_ofOld ``ExpL2
  checkExpected ``Tools.ShippingGen2.topShips_of_NC ``ExpL3
  checkExpected ``Tools.ShippingGen2.topShipsNC_of_topShips ``ExpL4
  checkExpected ``Tools.ShippingGen2.topShipsOld_of_NC ``ExpTopShipsOldOfNC
  checkExpected ``Tools.ShippingGen2.slotlessLeaf_topShipsNC_of_LB ``ExpS2LB
  checkExpected ``Tools.ShippingGen2.slotlessLeaf_topShipsNC ``ExpS2Run
  checkExpected ``Tools.ShippingGen2SlotlessTop.hierRefineCheck_linked_noRst ``ExpC1
  checkExpected ``Tools.ShippingGen2SlotlessTop.RunFacts.toNR ``ExpC3toNR
  checkExpected ``Tools.ShippingGen2SlotlessTop.outNameOk_of_run ``ExpOutNameOk
  checkExpected ``Tools.ShippingGen2SlotlessTop.machine_ships_hierC_runNR ``ExpC4
  checkExpected ``Tools.ShippingGen2.oneOutSl_topShipsNC ``ExpC5a
  -- mutants
  checkMutant ``Tools.ShippingGen2.TopShipsNC ``MutTopShipsNCrst
  checkMutant ``Tools.ShippingGen2.TopShips ``MutTopShipsRGclk
  checkMutant ``Tools.ShippingGen2.topShips_ofOld ``MutL2noClk
  checkMutant ``Tools.ShippingGen2.topShipsNC_of_topShips ``MutL4noRst
  checkMutant ``Tools.ShippingGen2.slotlessLeaf_topShipsNC ``MutS2RunRG
  checkMutant ``Tools.ShippingGen2SlotlessTop.hierRefineCheck_linked_noRst ``MutC1noR
  checkMutant ``Tools.ShippingGen2SlotlessTop.machine_ships_hierC_runNR ``MutC4noZ
  checkMutant ``Tools.ShippingGen2.oneOutSl_topShipsNC ``MutC5aOld
  checkMutant ``Tools.ShippingGen2.oneOutSl_topShipsNC ``MutC5aNoRst

/-! ## 2. Audit: full reachable closure (none of `TopShips`, `TopShipsOld`, L1-L3, `topShipsOld_of_NC`) -/

/-- The forbidden constants (S5 freeze §8.3 rev1; TOP_CONTRACT_REVISION §5 "no back door"). Since U-TOP-DEF `TopShips` is the R-G
contract and `TopShipsOld` the history text; the NC roots audited here are stated and proved without either, and without L1-L3. -/
def ncForbidden (n : Name) : Bool :=
  n == ``Tools.ShippingGen2.TopShips || n == ``Tools.ShippingGen2.TopShipsOld ||
  n == ``Tools.ShippingGen2.topShips_of_NC || n == ``Tools.ShippingGen2.topShipsOld_of_NC ||
  n == ``Tools.ShippingGen2.topShips_toOld || n == ``Tools.ShippingGen2.topShips_ofOld

/-- The body of a constant, read EXPLICITLY per kind (as `s5Body?`). -/
def ncBody? : ConstantInfo → Option Lean.Expr
  | .thmInfo t => some t.value
  | .defnInfo d => some d.value
  | .opaqueInfo o => some o.value
  | _ => none

structure NCReach where
  hit : Option (List Name) := none
  visited : Nat := 0
  noBody : Nat := 0
  opaques : Array Name := #[]
  deriving Inhabited

/-- Breadth-first search of the FULL dependency closure of `root` (as `s5Reach`) for a constant `forb` flags
(default: `ncForbidden`; §2c passes `ncSlForbidden`). -/
def ncReach (root : Name) (cap : Nat := 3000000) (forb : Name → Bool := ncForbidden) : MetaM NCReach := do
  let env ← getEnv
  let mut out : NCReach := {}
  let mut seen : NameSet := ({} : NameSet).insert root
  let mut queue : Array (Name × List Name) := #[(root, [root])]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    out := { out with visited := out.visited + 1 }
    if out.visited > cap then
      throwError "NC AUDIT INCOMPLETE at {root}: more than {cap} constants; non-reference NOT established"
    let some ci := env.find? c | continue
    let body := ncBody? ci
    if body.isNone then out := { out with noBody := out.noBody + 1 }
    if ci matches .opaqueInfo _ then out := { out with opaques := out.opaques.push c }
    let used := ci.type.getUsedConstants ++ (body.map (·.getUsedConstants)).getD #[]
    for u in used do
      if forb u then
        return { out with hit := some (path ++ [u]) }
      unless seen.contains u do
        seen := seen.insert u
        queue := queue.push (u, path ++ [u])
  return out

/-- The audited producers: C4, C5a and the U-TOP-S2 suppliers (and C1, which C4 uses). -/
def ncAudited : List Name :=
  [``Tools.ShippingGen2SlotlessTop.machine_ships_hierC_runNR, ``Tools.ShippingGen2.oneOutSl_topShipsNC,
   ``Tools.ShippingGen2.slotlessLeaf_topShipsNC_of_LB, ``Tools.ShippingGen2.slotlessLeaf_topShipsNC,
   ``Tools.ShippingGen2SlotlessTop.hierRefineCheck_linked_noRst]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- detector controls with the SAME search
  for (c, bad) in [(``Tests.Gen2.TopNCReachFixture.badDirect, true),
      (``Tests.Gen2.TopNCReachFixture.badIndirect, true), (``Tests.Gen2.TopNCReachFixture.badNC, true),
      (``Tests.Gen2.TopNCReachFixture.badOld, true),
      (``Tests.Gen2.TopNCReachFixture.goodUnrelated, false)] do
    let r ← ncReach c
    if bad && r.hit.isNone then throwError "NC AUDIT FAILED: the closure detector misses {c}"
    if !bad && r.hit.isSome then throwError "NC AUDIT FAILED: the closure detector flags {c}"
    logInfo m!"NC REACH CONTROL {c}: {toString r.hit}"
  for c in ncAudited do
    let r ← ncReach c
    if let some p := r.hit then
      throwError "NC AUDIT FAILED {c}: reaches TopShips / TopShipsOld / L1-L3 via {p}"
    logInfo m!"NC REACH {c}: none of TopShips, TopShipsOld, topShips_toOld, topShips_ofOld, topShips_of_NC, topShipsOld_of_NC in the closure (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques.size}: implementations of opaque/partial constants are not kernel terms and are not followed)"

/-! ## 2b. PAIR checks against the ORIGINAL declarations (S5 freeze §8 item 1; reviewer R1)

Comparator: `s5CheckPair` (Tests/Gen2/S5Check.lean:380-413) extended by DELETIONS and by LEVELS (a binder change
inside the conclusion, i.e. a deleted premise of the inner `∀ i …` telescope). At each level every binder of the
ORIGINAL is matched, in order, by the copy's binder of the same name (or its `renamed` image), with the same binder
info and the SAME type (`cmpEq`), except:
* `deleted`: original binders the copy drops, selected by name, or by position (0-based, in that level's telescope)
  for anonymous `→` premises; an optional string literal the deleted binder's type must mention pins WHICH premise;
* `added`: copy binders the original lacks — exactly this list, in this order;
* `renamed`: original name ↦ copy name, type NOT compared (the changed binder; as `s5CheckPair`);
* `retyped`: same name, type compared after replacing one constant by another.
Anything else (an extra, missing or reordered binder, a changed type, a listed deletion/addition that does not occur)
FAILS. After the last level the conclusion is compared exactly (`same`) or after one constant replacement (`repl`).
A level after the first is reached by a structural walk (`app`/`lam` compared part by part, every leaf by `cmpEq`)
that must meet EXACTLY ONE `∀` telescope. -/

inductive NCSel where
  | name (n : Name)
  | idx (k : Nat)
  deriving Inhabited

structure NCLevel where
  deleted : List (NCSel × Option String) := []
  added : List Name := []
  renamed : List (Name × Name) := []
  retyped : List (Name × Name × Name) := []
  deriving Inhabited

inductive NCConcl where
  | same
  | repl (a b : Name)
  deriving Inhabited

/-- Replace every occurrence of the constant `a` by `b` (same universe levels). -/
def ncReplConst (a b : Name) (e : Lean.Expr) : Lean.Expr :=
  e.replace fun s => match s with
    | .const n us => if n == a then some (.const b us) else none
    | _ => none

def ncMentionsStr (e : Lean.Expr) (s : String) : Bool :=
  (e.find? fun t => t == .lit (.strVal s)).isSome

def ncSelHit (i : Nat) (n : Name) : NCSel → Bool
  | .name m => m == n
  | .idx k => k == i

/-- A matched binder's type: not compared if renamed; compared after the constant replacement if retyped; else
compared as is. -/
def ncCmpBinder (what : String) (lv : NCLevel) (i : Nat) (nO : Name) (tC tO : Lean.Expr) : MetaM Unit := do
  if (lv.renamed.lookup nO).isSome then return
  if let some (_, a, b) := lv.retyped.find? (·.1 == nO) then
    cmpEq s!"{what} binder {nO} (retyped {a} ↦ {b})" tC (ncReplConst a b tO)
  else
    cmpEq s!"{what} binder {i} ({nO})" tC tO

/-- The conclusion after the last level. -/
def ncCmpConcl (what : String) (concl : NCConcl) (eO eC : Lean.Expr) : MetaM Unit := do
  if let .repl a b := concl then
    cmpEq s!"{what} conclusion ({a} ↦ {b})" eC (ncReplConst a b eO)
  else
    cmpEq s!"{what} conclusion" eC eO

mutual
/-- One level: the binder-by-binder comparison with the allowed changes `lv`. -/
partial def ncPairTele (what : String) (lv : NCLevel) (rest : List NCLevel) (concl : NCConcl)
    (eO eC : Lean.Expr) (i : Nat) (dels : List Nat) (adds : List Name) : MetaM Unit := do
  let eO := eO.consumeMData
  let eC := eC.consumeMData
  -- a deleted binder of the original
  if let .forallE nO tO bO biO := eO then
    let nO' := nO.eraseMacroScopes
    if let some k := lv.deleted.findIdx? (fun sl => ncSelHit i nO' sl.1) then
      if dels.contains k then
        throwError "NC PAIR FAILED {what}: deletion {k} selected twice (at original binder {i}, {nO'})"
      if let some lit := (lv.deleted[k]!).2 then
        unless ncMentionsStr tO lit do
          throwError "NC PAIR FAILED {what}: deleted binder {i} ({nO'}) does not mention {lit}:{indentExpr tO}"
      logInfo m!"NC PAIR {what}: original binder {i} ({nO'}) DELETED:{indentExpr tO}"
      return ← withLocalDecl nO biO tO fun x =>
        ncPairTele what lv rest concl (bO.instantiate1 x) eC (i + 1) (dels ++ [k]) adds
  -- an added binder of the copy
  if let .forallE nC tC bC biC := eC then
    let nC' := nC.eraseMacroScopes
    let expected? : Option Name := match eO with
      | .forallE nO .. => some ((lv.renamed.lookup nO.eraseMacroScopes).getD nO.eraseMacroScopes)
      | _ => none
    if lv.added.contains nC' && expected? != some nC' then
      return ← withLocalDecl nC biC tC fun y =>
        ncPairTele what lv rest concl eO (bC.instantiate1 y) i dels (adds ++ [nC'])
  match eO, eC with
  | .forallE nO tO bO biO, .forallE nC tC bC biC =>
    let nO' := nO.eraseMacroScopes
    let ren := lv.renamed.lookup nO'
    let expName := ren.getD nO'
    unless nC.eraseMacroScopes == expName do
      throwError "NC PAIR FAILED {what}: binder {i} is {nC.eraseMacroScopes}, expected {expName} (original {nO'})"
    unless biC == biO do
      throwError "NC PAIR FAILED {what}: binder {expName} has a different binder info"
    ncCmpBinder what lv i nO' tC tO
    withLocalDecl nO biO tO fun x =>
      ncPairTele what lv rest concl (bO.instantiate1 x) (bC.instantiate1 x) (i + 1) dels adds
  | .forallE nO .., _ =>
    throwError "NC PAIR FAILED {what}: the copy lacks original binder {i} ({nO.eraseMacroScopes}), not listed as deleted"
  | _, .forallE nC .. =>
    throwError "NC PAIR FAILED {what}: extra copy binder {nC.eraseMacroScopes}, not listed as added (here)"
  | _, _ =>
    unless dels.length == lv.deleted.length do
      throwError "NC PAIR FAILED {what}: {dels.length} of the {lv.deleted.length} listed deletions occur"
    unless adds == lv.added do
      throwError "NC PAIR FAILED {what}: added binders {adds}, expected exactly {lv.added}"
    if rest.isEmpty then
      ncCmpConcl what concl eO eC
    else
      let k ← ncPairWalk what rest concl eO eC
      unless k == 1 do
        throwError "NC PAIR FAILED {what}: the next level met {k} ∀-telescopes, expected exactly 1"

/-- The structural walk to the next level's `∀` telescope; returns how many telescopes it met. -/
partial def ncPairWalk (what : String) (lvs : List NCLevel) (concl : NCConcl) (eO eC : Lean.Expr) :
    MetaM Nat := do
  match eO.consumeMData, eC.consumeMData, lvs with
  | o@(.forallE ..), c@(.forallE ..), lv :: rest =>
    ncPairTele what lv rest concl o c 0 [] []
    return 1
  | .app fO aO, .app fC aC, _ =>
    let k₁ ← ncPairWalk what lvs concl fO fC
    let k₂ ← ncPairWalk what lvs concl aO aC
    return k₁ + k₂
  | .lam nO tO bO biO, .lam nC tC bC biC, _ =>
    unless nO.eraseMacroScopes == nC.eraseMacroScopes && biO == biC do
      throwError "NC PAIR FAILED {what}: λ-binder {nC.eraseMacroScopes} vs original {nO.eraseMacroScopes}"
    cmpEq s!"{what} λ-binder {nO.eraseMacroScopes}" tC tO
    withLocalDecl nO biO tO fun x => ncPairWalk what lvs concl (bO.instantiate1 x) (bC.instantiate1 x)
  | o, c, _ =>
    cmpEq s!"{what} (walk)" c o
    return 0
end

/-- The PAIR check of `copy` against `orig` (types, or definition values with `useValue`). -/
def ncCheckPair (orig copy : Name) (lvs : List NCLevel) (concl : NCConcl) (useValue : Bool := false) :
    MetaM Unit := do
  let ciO ← getConstInfo orig
  let ciC ← getConstInfo copy
  unless ciO.levelParams.length == ciC.levelParams.length do
    throwError "NC PAIR FAILED {copy}: universe parameters {ciC.levelParams} vs {ciO.levelParams}"
  let mut eO := ciO.type
  let mut eC := ciC.type
  if useValue then
    let some vO := ciO.value? | throwError "NC PAIR FAILED {copy}: {orig} has no definition value"
    let some vC := ciC.value? | throwError "NC PAIR FAILED {copy}: {copy} has no definition value"
    eO := vO
    eC := vC
  let what := s!"{copy} vs {orig}"
  let k ← ncPairWalk what lvs concl eO eC
  unless k == 1 do
    throwError "NC PAIR FAILED {what}: met {k} top ∀-telescopes, expected exactly 1"
  logInfo m!"NC PAIR OK {copy} against {orig}: only the listed binder changes ({lvs.length} level(s))"

/-! ### U-TOP-S2 (run level): correspondence table

`slotlessLeaf_ships` (SlotlessLeaf:438) : `SlotlessLeafStmt L` (SlotlessLeaf:425-435, unfolded) versus
`slotlessLeaf_topShipsNC` (Tools/ShippingGen2TopNC.lean:305). Its conclusion is the FIRST conjunct of the original's
(`TopShips ↦ TopShipsNC`). Binder infos are not compared (the `Stmt` binds everything explicitly).

| # | original binder (`SlotlessLeafStmt`)                     | copy        | why dropped                                   |
|---|----------------------------------------------------------|-------------|-----------------------------------------------|
| 0-4 | `ι`, `dom`, `mref`, `cref`, `L`                         | same names  |                                               |
| 5-8 | `p`, `mctx`, `cctx`, `w`                                | same names  |                                               |
| 9 | `w1 : Void IO.RealWorld`                                 | DROPPED     | occurs only in the dropped `RunsTo` (19)      |
| 10-12 | `raw`, `b`, `D`                                       | same names  |                                               |
| 13 | `LeafDataOk p`                                          | `hdata`     |                                               |
| 14 | `ExtInS p`                                              | DROPPED     | used only for the `ChildShips` conjunct, which the copy does not conclude |
| 15 | `p.d.shape.insts = []`                                  | `hnoI`      |                                               |
| 16 | `p.d.shape.layout.slots = []`                           | `hsl0`      |                                               |
| 17 | `AdmCtx L.O.quiet mctx cctx`                            | `hA`        |                                               |
| 18 | `JQC L.O (dv w) w`                                      | DROPPED     | unused (`_` in `slotlessLeaf_ships`)          |
| 19 | `RunsTo (synthesizeCombinationalCore …) … w (raw, D) w1`| DROPPED     | unused (`_`)                                  |
| 20 | `b = dropZeroWidthModule raw ∨ b = mergeChecked …`      | `hpost`     |                                               |
| 21 | `MachineDefines … p.decl p.d.shape`                     | DROPPED     | unused (`_`)                                  |
| 22 | `MachineTaken L mctx cctx (dv w + 1) …`                 | `ran`       |                                               |
| 23 | `n`                                                     | `n`         |                                               |

So the copy's binders are the original's minus exactly JQC / RunsTo / MachineDefines (the unused ones) PLUS `w1`
(only in `RunsTo`) and `ExtInS` (only for `ChildShips`). The check pins each dropped binder by its type's head
constant (`w1` by having `w`'s type) and every kept binder by name and type. -/

inductive NCCorr where
  | keep (copyName : Name)
  | drop (head : Name)
  | dropSameTypeAs (k : Nat)
  deriving Inhabited

def ncCheckCorr (orig copy : Name) (table : List (String × NCCorr)) (conclA conclB : Name) : MetaM Unit := do
  let ciO ← getConstInfo orig
  let ciC ← getConstInfo copy
  forallTelescopeReducing ciO.type fun xs bodyO => do
    forallTelescope ciC.type fun ys bodyC => do
      unless xs.size == table.length do
        throwError "NC CORR FAILED {copy}: {orig} has {xs.size} binders, the table lists {table.length}"
      let mut kept : Array Lean.Expr := #[]
      let mut names : Array Name := #[]
      for k in [0:xs.size] do
        let x := xs[k]!
        let (lbl, c) := table[k]!
        let ty ← inferType x
        match c with
        | .keep n =>
          kept := kept.push x
          names := names.push n
        | .drop hd =>
          unless ty.getAppFn.isConstOf hd do
            throwError "NC CORR FAILED {copy}: dropped binder {k} ({lbl}) has type{indentExpr ty}\nexpected head {hd}"
          logInfo m!"NC CORR {copy}: original binder {k} ({lbl}) DROPPED:{indentExpr ty}"
        | .dropSameTypeAs j =>
          unless ty == (← inferType xs[j]!) do
            throwError "NC CORR FAILED {copy}: dropped binder {k} ({lbl}) does not have binder {j}'s type"
          logInfo m!"NC CORR {copy}: original binder {k} ({lbl}) DROPPED:{indentExpr ty}"
      unless kept.size == ys.size do
        throwError "NC CORR FAILED {copy}: {ys.size} binders, the table keeps {kept.size}"
      for k in [0:ys.size] do
        let yd ← ys[k]!.fvarId!.getDecl
        unless yd.userName.eraseMacroScopes == names[k]! do
          throwError "NC CORR FAILED {copy}: binder {k} is {yd.userName.eraseMacroScopes}, expected {names[k]!}"
        cmpEq s!"{copy} binder {names[k]!} vs {orig}" yd.type ((← inferType kept[k]!).replaceFVars kept ys)
      unless bodyO.isAppOfArity ``And 2 do
        throwError "NC CORR FAILED {copy}: {orig}'s conclusion is not a conjunction:{indentExpr bodyO}"
      cmpEq s!"{copy} conclusion vs {orig}'s first conjunct ({conclA} ↦ {conclB})" bodyC
        (ncReplConst conclA conclB (bodyO.appFn!.appArg!.replaceFVars kept ys))
  logInfo m!"NC CORR OK {copy} against {orig}: kept/dropped exactly as the table"

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- C1 (freeze §5 C1): `hrstIn`, `hrstZ`, `hfitR` deleted; `hnoR` added last; conclusion unchanged.
  ncCheckPair ``Tools.ShippingHierOptRun.hierRefineCheck_linked
    ``Tools.ShippingGen2SlotlessTop.hierRefineCheck_linked_noRst
    [{ deleted := [(.name `hrstIn, some "rst"), (.name `hrstZ, some "rst"), (.name `hfitR, none)],
       added := [`hnoR] }] .same
  -- C2 (freeze §5 C2): definition values; in the inner `∀ i …` telescope the premises 10 (`∀ t, ins t "rst" = 0`)
  -- and 11 (`∀ t st, seedIn b ins t st "clk" = 0`) deleted (Defs:283); nothing else.
  ncCheckPair ``Tools.ShippingGen2.TopShips ``Tools.ShippingGen2.TopShipsNC
    [{ deleted := [(.idx 10, some "rst"), (.idx 11, some "clk")] }] .same (useValue := true)
  -- C4 (freeze §5 C4): `hinitW` deleted; `hslots`, `hsl0`, `hnR`, `hnC`, `hZ` added; `facts` retyped
  -- `RunFacts ↦ RunFactsNR`; in the conclusion's inner telescope the premises 10 (rst) and 11 (clk) deleted (:1145).
  ncCheckPair ``Tools.ShippingSrm33.machine_ships_hierC_run ``Tools.ShippingGen2SlotlessTop.machine_ships_hierC_runNR
    [{ deleted := [(.name `hinitW, none)], added := [`hslots, `hsl0, `hnR, `hnC, `hZ],
       retyped := [(`facts, ``Tools.ShippingGuardsSound.RunFacts, ``Tools.ShippingGen2SlotlessTop.RunFactsNR)] },
     { deleted := [(.idx 10, some "rst"), (.idx 11, some "clk")] }] .same
  -- C5a (freeze §5 C5a): `hsl` ↦ `hsl0`, `hrst` added; conclusion `TopShips ↦ TopShipsNC`.
  ncCheckPair ``Tools.ShippingGen2.oneOut_topShipsO ``Tools.ShippingGen2.oneOutSl_topShipsNC
    [{ renamed := [(`hsl, `hsl0)], added := [`hrst] }] (.repl ``Tools.ShippingGen2.TopShips ``Tools.ShippingGen2.TopShipsNC)
  -- U-TOP-S2 pure: `hinA` added; conclusion `TopShips ↦ TopShipsNC`.
  ncCheckPair ``Tools.ShippingGen2.slotlessLeaf_topShips_of_LB ``Tools.ShippingGen2.slotlessLeaf_topShipsNC_of_LB
    [{ added := [`hinA] }] (.repl ``Tools.ShippingGen2.TopShips ``Tools.ShippingGen2.TopShipsNC)
  -- U-TOP-S2 run level: the correspondence table above.
  ncCheckCorr ``Tools.ShippingGen2.slotlessLeaf_ships ``Tools.ShippingGen2.slotlessLeaf_topShipsNC
    [("ι", .keep `ι), ("dom", .keep `dom), ("mref", .keep `mref), ("cref", .keep `cref), ("L", .keep `L),
     ("p", .keep `p), ("mctx", .keep `mctx), ("cctx", .keep `cctx), ("w", .keep `w), ("w1", .dropSameTypeAs 8),
     ("raw", .keep `raw), ("b", .keep `b), ("D", .keep `D), ("LeafDataOk", .keep `hdata),
     ("ExtInS", .drop ``Tools.ShippingGen2.ExtInS), ("insts = []", .keep `hnoI), ("slots = []", .keep `hsl0),
     ("AdmCtx", .keep `hA), ("JQC", .drop ``Tools.ShippingChildCacheA.JQC),
     ("RunsTo", .drop ``Tools.ShippingEntrySoundness.RunsTo), ("hpost", .keep `hpost),
     ("MachineDefines", .drop ``Tools.ShippingMachineEntry.MachineDefines), ("MachineTaken", .keep `ran),
     ("n", .keep `n)]
    ``Tools.ShippingGen2.TopShips ``Tools.ShippingGen2.TopShipsNC

/-! ## 2c. Second audit: no old-boundary slotless fact in the closure (S5 freeze §8 item 2; reviewer R2)

The SAME BFS (`ncReach`, full reachable closure: type and explicit body of every reached constant, every namespace)
with the forbidden set of S5Check's `s5Forbidden`: `Tools.ShippingSlotlessClk.SeqKid` and every constant with prefix
`Tools.ShippingSlotlessClk.` or `Tools.ShippingSlotlessKidFacts.`. Every hit is a FAILURE (no whitelist).
Limitation (as §2): implementations of opaque/partial constants are not kernel terms and are not followed. -/

/-- The forbidden constants of the second audit (= `s5Forbidden`, S5Check:466-467; `SeqKid` is in the first prefix). -/
def ncSlForbidden (n : Name) : Bool :=
  n == ``Tools.ShippingSlotlessClk.SeqKid ||
  (`Tools.ShippingSlotlessClk).isPrefixOf n || (`Tools.ShippingSlotlessKidFacts).isPrefixOf n

/-- The audited roots of the second audit: C1, C4, C5a and the U-TOP-S2 producers. -/
def ncSlAudited : List Name :=
  [``Tools.ShippingGen2SlotlessTop.hierRefineCheck_linked_noRst,
   ``Tools.ShippingGen2SlotlessTop.machine_ships_hierC_runNR, ``Tools.ShippingGen2.oneOutSl_topShipsNC,
   ``Tools.ShippingGen2.slotlessLeaf_topShipsNC_of_LB, ``Tools.ShippingGen2.slotlessLeaf_topShipsNC]

set_option maxHeartbeats 0 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- detector controls with the SAME search and the SAME forbidden set
  for (c, bad) in [(``Tests.Gen2.TopNCSlReachFixture.badDirect, true),
      (``Tests.Gen2.TopNCSlReachFixture.badIndirect, true), (``Tests.Gen2.TopNCSlReachFixture.badKidFacts, true),
      (``Tests.Gen2.TopNCSlReachFixture.goodUnrelated, false)] do
    let r ← ncReach c (forb := ncSlForbidden)
    if bad && r.hit.isNone then throwError "NC SL AUDIT FAILED: the closure detector misses {c}"
    if !bad && r.hit.isSome then throwError "NC SL AUDIT FAILED: the closure detector flags {c}"
    logInfo m!"NC SL REACH CONTROL {c}: {toString r.hit}"
  for c in ncSlAudited do
    let r ← ncReach c (forb := ncSlForbidden)
    if let some p := r.hit then
      throwError "NC SL AUDIT FAILED {c}: reaches an old-boundary slotless constant via {p}"
    logInfo m!"NC SL REACH {c}: no Tools.ShippingSlotlessClk.* (incl. SeqKid) / Tools.ShippingSlotlessKidFacts.* in the closure (visited {r.visited}, no-body {r.noBody}, opaque {r.opaques.size}: implementations of opaque/partial constants are not kernel terms and are not followed)"

end Tests.Gen2.TopNCCheck

/-! ## 3. P3-core: an execution control of A2 on a concrete clock-free module -/
namespace Tests.Gen2.TopNCControl
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierOpen
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingSeqOptSoundness (seedIn)
open Sparkle.IR.RegDedup (declWidth)
open Sparkle.IR.Machine (SlotField)
open Tools.ShippingGen2SlotlessParent (NoTouchZ slSeedZ slSeedZ_agree runModuleTG_seed_offZ)

/-- The comb child `c0`: `y := i`. -/
def c0 : Module :=
  { name := "c0", inputs := [⟨"i", .bitVector 8⟩], outputs := [⟨"y", .bitVector 8⟩],
    wires := [⟨"i", .bitVector 8⟩, ⟨"y", .bitVector 8⟩], body := [.assign "y" (.ref "i")] }

/-- The case-(C) module `m0`: input `a` only (no `"clk"`/`"rst"`); an instance `k` of `c0` reading `a` into `x`;
`o := x`. -/
def m0 : Module :=
  { name := "m0", inputs := [⟨"a", .bitVector 8⟩], outputs := [⟨"o", .bitVector 8⟩],
    wires := [⟨"a", .bitVector 8⟩, ⟨"x", .bitVector 8⟩, ⟨"o", .bitVector 8⟩],
    body := [.inst "c0" "k" [("i", .ref "a"), ("y", .ref "x")], .assign "o" (.ref "x")] }

def d0 : Design := { topModule := "m0", modules := [c0] }

/-- The input stream: `a` at cycle `t` is `(t + 3) % 256`. -/
def ins0 : Nat → String → Nat := fun t _ => (t + 3) % 256

/-- The zero kid state at depth 1 (the comb child's own state at depth 0 is zero too). -/
def kids0 : String → KT 1 :=
  fun _ => KState.mk (fun _ => 0) (fun _ _ => 0) (fun _ => KidState.mk (fun _ => 0) (fun _ _ => 0))

/-- The zero start state (`st0 := 0`, `mems := 0`, `kids0`). -/
def s0 : KState (KT 1) := ⟨fun _ => 0, fun _ _ => 0, kids0⟩

/-! ### (i) the inner premises of `TopShipsNC` not mentioning the package witnesses, at `m0` -/

/-- passthrough over `regs = []` -/
theorem p3_pass : ∀ t st r, r ∈ ([] : List String) → seedIn m0 ins0 t st r = st r := by
  intro t st r h
  simp at h

/-- slot inits over `slots = []` -/
theorem p3_slots : ∀ (k : Nat) (r : String) (f : SlotField), ([] : List String)[k]? = some r →
    ([] : List SlotField)[k]? = some f → s0.st r = f.init := by
  intro k r f h _
  simp at h

/-- `ResetNk 1 m0 d0 kids0` -/
theorem p3_reset : Tools.ShippingMachineShipsDepth.ResetNk 1 m0 d0 kids0 := by
  unfold Tools.ShippingMachineShipsDepth.ResetNk
  intro iname mc hex hf
  obtain ⟨conns, hm⟩ := hex
  have hname : mc.name = "c0" := by
    rcases List.mem_cons.mp hm with h | h
    · injection h with h1 <;> (try exact h1)
    · rw [List.mem_singleton] at h
      cases h
  rw [hname] at hf
  have hmod : Sparkle.IR.Machine.moduleByName d0.modules "c0" = some c0 := by decide +kernel
  rw [hmod] at hf
  have hc : mc = c0 := (Option.some.inj hf).symm
  subst hc
  unfold Tools.ShippingMachineDepth.ResetN
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro r c rs inp init h
    simp [c0] at h
  · intro nm i
    rfl
  · intro nm aw dw c wa wd we ra rd cr ew er h
    simp [c0] at h
  · first
      | (intro mn iname' conns' mc' h; simp [c0] at h)
      | simp [c0]

/-- the input fit -/
theorem p3_insFit : ∀ t x, x ∈ m0.inputs.map (·.name) → ins0 t x < 2 ^ declWidth m0 x := by
  intro t x hx
  have hxa : x = "a" := by simpa [m0] using hx
  subst hxa
  have hw : declWidth m0 "a" = 8 := by decide +kernel
  rw [hw]
  show (t + 3) % 256 < 2 ^ 8
  exact Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)

/-- the state fit -/
theorem p3_stFit : ∀ x ∈ (Sparkle.IR.HierCheck.openIns m0).map (·.name),
    x ∉ bodyInstOuts (childMap d0.modules) m0.body → s0.st x < 2 ^ declWidth m0 x :=
  fun _ _ _ => Nat.two_pow_pos _

/-! ### (ii) A2 exercised: the zeroed-seed run, transferred, its conclusion used -/

theorem p3_noTouch : NoTouchZ ["rst", "clk"] m0.body := by
  intro st hst
  rcases List.mem_cons.mp hst with rfl | hst
  · refine Or.inr ⟨"c0", "k", [("i", .ref "a"), ("y", .ref "x")], rfl, fun c hc w hw => ?_⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · have hwa : w = "a" := by simpa using hw.symm
      subst hwa
      simp
    · rw [List.mem_singleton] at hc
      subst hc
      have hwx : w = "x" := by simpa using hw.symm
      subst hwx
      simp
  · rw [List.mem_singleton] at hst
    subst hst
    refine Or.inl ⟨"o", .ref "x", rfl, by simp, fun z hz hzr => ?_⟩
    simp only [Sparkle.IR.Reorder.refsOf, List.mem_singleton] at hzr
    subst hzr
    simp at hz

/-- The run at the zeroed seed exists (computed). -/
theorem p3_runZ_isSome :
    (runModuleTG (KSn (childMap d0.modules) 1) (declWidth m0) (childMap d0.modules) m0.body
      (slSeedZ m0 ins0) 2 s0).isSome = true := by
  decide +kernel

/-- Its outputs at `"o"` (computed): cycle 0 reads `a = 4` (seed index 1), cycle 1 reads `a = 3`. -/
theorem p3_runZ_o :
    (runModuleTG (KSn (childMap d0.modules) 1) (declWidth m0) (childMap d0.modules) m0.body
      (slSeedZ m0 ins0) 2 s0).map (fun es => es.map (fun e => e "o")) = some [4, 3] := by
  decide +kernel

/-- Direct evaluation of the `seedIn` run (the cross-check). -/
theorem p3_runS_o :
    (runModuleTG (KSn (childMap d0.modules) 1) (declWidth m0) (childMap d0.modules) m0.body
      (seedIn m0 ins0) 2 s0).map (fun es => es.map (fun e => e "o")) = some [4, 3] := by
  decide +kernel

/-- **A2's conclusion used**: from the zeroed-seed run, A2 gives a run at `seedIn m0 ins0` whose outputs at `"o"`
are `[4, 3]` (derived through A2's agreement off `Z`, not by evaluating the `seedIn` run). -/
theorem p3_out : ∃ envs₂, runModuleTG (KSn (childMap d0.modules) 1) (declWidth m0) (childMap d0.modules) m0.body
    (seedIn m0 ins0) 2 s0 = some envs₂ ∧ envs₂.map (fun e => e "o") = [4, 3] := by
  obtain ⟨envs₁, h₁⟩ := Option.isSome_iff_exists.mp p3_runZ_isSome
  have hv₁ : envs₁.map (fun e => e "o") = [4, 3] := by
    have h := p3_runZ_o
    rw [h₁] at h
    exact Option.some.inj h
  obtain ⟨envs₂, h₂, hlen, hpt⟩ := runModuleTG_seed_offZ (KSn (childMap d0.modules) 1)
    (KSn_local (childMap d0.modules) 1) (declWidth m0) (childMap d0.modules) p3_noTouch
    (slSeedZ_agree m0 ins0) 2 s0 envs₁ h₁
  refine ⟨envs₂, h₂, ?_⟩
  rw [← hv₁]
  refine List.ext_getElem (by simp [hlen]) (fun j hj₂ hj₁ => ?_)
  simp only [List.getElem_map]
  exact hpt j (by simpa using hj₁) (by simpa using hj₂) "o" (by simp)

/-- **Cross-check**: the A2-derived outputs agree with direct evaluation of the `seedIn` run. -/
theorem p3_cross : ∀ envs₂, runModuleTG (KSn (childMap d0.modules) 1) (declWidth m0) (childMap d0.modules)
    m0.body (seedIn m0 ins0) 2 s0 = some envs₂ → envs₂.map (fun e => e "o") = [4, 3] := by
  intro envs₂ h
  have h' := p3_runS_o
  rw [h] at h'
  exact Option.some.inj h'

/-! ### (iii) the OLD clk binder (Defs:283) is refuted at `m0`; every premise in (i) holds -/

theorem p3_old_clk_refuted : ¬ (∀ t st, seedIn m0 ins0 t st "clk" = 0) :=
  Tools.ShippingGen2.not_seedIn_clk_zero ins0 (by simp [m0])

end Tests.Gen2.TopNCControl

/-! ## 4. Axioms -/
#print axioms Tools.ShippingGen2.topShips_toOld
#print axioms Tools.ShippingGen2.topShips_ofOld
#print axioms Tools.ShippingGen2.topShips_ofOld_wired
#print axioms Tools.ShippingGen2.topShips_of_NC
#print axioms Tools.ShippingGen2.topShipsNC_of_topShips
#print axioms Tools.ShippingGen2.topShipsOld_of_NC
#print axioms Tools.ShippingGen2.slotlessLeaf_topShipsNC_of_LB
#print axioms Tools.ShippingGen2.slotlessLeaf_topShipsNC
#print axioms Tools.ShippingGen2.slotlessLeaf_topShips_of_NC
#print axioms Tools.ShippingGen2SlotlessTop.hierRefineCheck_linked_noRst
#print axioms Tools.ShippingGen2SlotlessTop.RunFacts.toNR
#print axioms Tools.ShippingGen2SlotlessTop.outNameOk_of_run
#print axioms Tools.ShippingGen2SlotlessTop.seqRegsL_nil_of_noTouch
#print axioms Tools.ShippingGen2SlotlessTop.machine_ships_hierC_runNR
#print axioms Tools.ShippingGen2.oneOutSl_topShipsNC
#print axioms Tests.Gen2.TopNCControl.p3_reset
#print axioms Tests.Gen2.TopNCControl.p3_insFit
#print axioms Tests.Gen2.TopNCControl.p3_noTouch
#print axioms Tests.Gen2.TopNCControl.p3_out
#print axioms Tests.Gen2.TopNCControl.p3_cross
#print axioms Tests.Gen2.TopNCControl.p3_old_clk_refuted

run_cmd Lean.Elab.Command.liftTermElabM do
  for c in [``Tools.ShippingGen2.TopShipsNC, ``Tools.ShippingGen2.TopShipsOld, ``Tools.ShippingGen2.tc_seedIn_in,
      ``Tools.ShippingGen2.topShips_toOld, ``Tools.ShippingGen2.topShips_ofOld, ``Tools.ShippingGen2.topShips_ofOld_wired,
      ``Tools.ShippingGen2.topShips_of_NC, ``Tools.ShippingGen2.topShipsNC_of_topShips,
      ``Tools.ShippingGen2.topShipsOld_of_NC, ``Tools.ShippingGen2.slotlessLeaf_topShipsNC_of_LB,
      ``Tools.ShippingGen2.slotlessLeaf_topShipsNC, ``Tools.ShippingGen2.slotlessLeaf_topShips_of_NC,
      ``Tools.ShippingGen2.machineWired_clk_rst_in, ``Tools.ShippingGen2.clk_rst_in_b_of_wired,
      ``Tools.ShippingGen2.b_inputs_of_hpost,
      ``Tools.ShippingGen2SlotlessTop.hierRefineCheck_linked_noRst, ``Tools.ShippingGen2SlotlessTop.RunFacts.toNR,
      ``Tools.ShippingGen2SlotlessTop.outNameOk_of_run, ``Tools.ShippingGen2SlotlessTop.seqRegsL_nil_of_noTouch,
      ``Tools.ShippingGen2SlotlessTop.machine_ships_hierC_runNR, ``Tools.ShippingGen2.oneOutSl_topShipsNC,
      ``Tests.Gen2.TopNCControl.p3_pass, ``Tests.Gen2.TopNCControl.p3_slots, ``Tests.Gen2.TopNCControl.p3_reset,
      ``Tests.Gen2.TopNCControl.p3_insFit, ``Tests.Gen2.TopNCControl.p3_stFit,
      ``Tests.Gen2.TopNCControl.p3_noTouch, ``Tests.Gen2.TopNCControl.p3_runZ_isSome,
      ``Tests.Gen2.TopNCControl.p3_runZ_o, ``Tests.Gen2.TopNCControl.p3_runS_o, ``Tests.Gen2.TopNCControl.p3_out,
      ``Tests.Gen2.TopNCControl.p3_cross, ``Tests.Gen2.TopNCControl.p3_old_clk_refuted] do
    Tests.Gen3.ExpectedType.checkAxioms c
