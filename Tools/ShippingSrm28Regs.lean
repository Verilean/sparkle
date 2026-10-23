import Tools.ShippingMachineDepthRun
import Tools.ShippingSrm25Init
set_option autoImplicit false
-- BUILT (unit SRM28): dev runs r2 (exit 0); the final-SHA rebuild in REPORT-SRM28.md is the only final evidence.
-- SCOPE (generic, no topshare instance): `MachineWired` (Tools/ShippingMachineEntry.lean) now EXPORTS, as its 19th conjunct, SRM25's source fact for its own `m`, `regs`, UNCONDITIONALLY
-- (also for shape.insts ≠ []); it is PROVED at the producer from closeMachine's body + closeInsts_some / closeInstsG_some.  Here: (1) that conjunct read as `SourceRegsAreSlots m regs slots`;
-- (2) G5 `ShippedRegsAreSlots b regs slots` from `hierGate b`, `b.body = m.body` and the wiring (no K0N, no K1, no hregsNd/hlen); (3) `ComposedNWRegs`: ComposedNW with ONE extra conjunct `P regs`
-- on the SAME `regs` witness, and the lifting lemma from `ComposedNW`.  K1 (regs = psN), G1, G3, hsk, FitTree, hRK, hst facts, hW and every other binder are untouched.  No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm28
open Lean hiding Module Expr
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.Compiler.Elab
open Sparkle.Core.Domain Sparkle.Core.Signal
open Sparkle.IR.RefineCheck (hierGate)
open Sparkle.IR.Machine (OutField SlotField moduleByName outNameOk)
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto Tools.ShippingMixedSourceBridge
open Tools.ShippingHierState Tools.ShippingHierStateG Tools.ShippingHierMono
open Tools.ShippingMachineDepth Tools.ShippingMachineDepthChild
open Tools.ShippingMachineLinked (childMap)
open Tools.ShippingMachineDepthRun
open Tools.ShippingSrm25Init (SourceRegsAreSlots shippedRegsAreSlots_of_source)
open Tools.ShippingSrm22Width (ShippedRegsAreSlots)

/-- **PROVED**: `MachineWired` exports the source fact for its own `regs` (any machine, with or without calls). -/
theorem sourceRegsAreSlots_of_wired_all {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m : Module} {dsn : Design} {regs lets : List String}
    (hW : MachineWired declName shape ids cache m dsn regs lets) :
    SourceRegsAreSlots m regs shape.layout.slots := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hall⟩ := hW
  exact hall

/-- **PROVED**: G5 for the exported `regs` witness, from `hierGate b`, `b.body = m.body` and the wiring alone. -/
theorem shippedRegsAreSlots_of_wired_all {declName : Name} {shape : MachineShape} {ids : List FVarId}
    {cache : IO.Ref (ExprStructMap String)} {m b : Module} {dsn : Design} {regs lets : List String}
    (hgate : hierGate b = true) (hb : b.body = m.body)
    (hW : MachineWired declName shape ids cache m dsn regs lets) :
    ShippedRegsAreSlots b regs shape.layout.slots :=
  shippedRegsAreSlots_of_source hgate regs shape.layout.slots
    (fun r c rs inp init hm => sourceRegsAreSlots_of_wired_all hW r c rs inp init (hb ▸ hm))

/-- `ComposedNW` (Tools/ShippingMachineDepthRun.lean:34) with ONE extra conjunct `P regs` on the same `regs` witness. -/
def ComposedNWRegs (n : Nat) (declName : Name) (d : MachineData) (kD : Nat) (m : Module) (dsn : Design)
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
      (∀ (iname : String) (mc : Module), (∃ conns, Stmt.inst mc.name iname conns ∈ m.body) →
        moduleByName dsn.modules mc.name = some mc → ResetN dsn n mc (kids iname)) →
      ∃ envs, runModuleTG (KSn (childMap dsn.modules) n) (Tools.ShippingEntrySoundness.weOf m)
          (childMap dsn.modules) m.body seed T ⟨st0, mems, kids⟩ = some envs ∧
        envs.length = T ∧
        ∀ j (hj : j < envs.length) (k : Nat) (o : OutField) (f : Nat → Nat),
          d.shape.layout.outs[k]? = some o → (src i bools bits)[k]? = some f →
          (envs[j]'hj) o.name = f j

/-- **PROVED**: a `ComposedNW` whose `regs` witness satisfies `P` (from the wiring) is a `ComposedNWRegs`; the witness is the one of `h`. -/
theorem composedNWRegs_of_composedNW {n : Nat} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    (P : List String → Prop)
    (h : ComposedNW n declName d kD m dsn dom src ext extB)
    (hP : ∀ (ids : List FVarId) (cache : IO.Ref (ExprStructMap String)) (regs lets : List String),
      regs.Nodup → regs.length = d.ss.length →
      MachineWired declName d.shape ids cache m dsn regs lets → P regs) :
    ComposedNWRegs n declName d kD m dsn dom src ext extB P := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩ := h
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, hP ids cache regs lets rnd rlen wired,
    lets, llen, wired, H⟩

/-- **PROVED**: forgetting `P`. -/
theorem ComposedNWRegs.toNW {n : Nat} {declName : Name} {d : MachineData} {kD : Nat}
    {m : Module} {dsn : Design} {ι : Type} {dom : ι → DomainConfig}
    {src : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)}
    {ext : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) →
      (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)}
    {extB : (i : ι) → (Nat → Signal (dom i) Bool) →
      ((j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) → Nat → Signal (dom i) Bool}
    {P : List String → Prop}
    (h : ComposedNWRegs n declName d kD m dsn dom src ext extB P) :
    ComposedNW n declName d kD m dsn dom src ext extB := by
  obtain ⟨ids, nd, len, cache, regs, rnd, rlen, -, lets, llen, wired, H⟩ := h
  exact ⟨ids, nd, len, cache, regs, rnd, rlen, lets, llen, wired, H⟩

end Tools.ShippingSrm28

#print axioms Tools.ShippingSrm28.sourceRegsAreSlots_of_wired_all
#print axioms Tools.ShippingSrm28.shippedRegsAreSlots_of_wired_all
#print axioms Tools.ShippingSrm28.composedNWRegs_of_composedNW
#print axioms Tools.ShippingSrm28.ComposedNWRegs.toNW
