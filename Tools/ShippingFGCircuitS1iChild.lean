import Tools.ShippingFGCircuitS1iRoots
import Tools.ShippingGen5DCEntryT
import Tools.ShippingGen5DCEntryN
import Tools.ShippingGen5DCEntryR
set_option autoImplicit false
-- FG circuit pilot S1i, unit 4: the first step toward a non-leaf root: `TopShips` moves from the core design `D` to the printed design `D'` for a module WITH instances, and a computable checker for the side conditions. No `sorry`, no `axiom`, no `native_decide`, no TRUSTED.

/-! # S1i-4: `DesignTransport` for a root with child instances (first step)

For a register leaf `designTransport_of_leaf` shows `TopShips p n X b raw D → TopShips p n X b raw D'` because `raw`, `b` and `checkedOptimize b` are instance-free: the design is irrelevant (`topShips_design_irrel`).
With child instances the design is NOT irrelevant: `TopShips` reads `D` through `childMap D.modules` (the oracle `KSn` and `runModuleTG`), `ResetNk n raw D kids` and `bodyInstOuts (childMap D.modules) b.body`.
The printed design is `D' = topMap … D` (`PostEntry`): the top module (named `raw.name`) is replaced, every other module is looked up as before.  So the transport holds when no instance below the top, in `raw`, in `b` and in `checkedOptimize b`, names the top module (`NoRawBelow`):
* `topShips_transport`: `TopShips p n X b raw D → TopShips p n X b raw D'` from `PostEntry`, `NoRawBelow D raw.name (n+1) raw`, `NoRawBelow D raw.name (n+1) (checkedOptimize b)` and "no instance of `b.body` names the top".
  The pieces are the existing conditional lemmas (`resetNk_transport`, `runModuleTG_transport`, `postEntry_lookup_ne`); what is new is the lift to `TopShips` and `bodyInstOuts`.
* `noRawBelowB` is a computable checker for `NoRawBelow` (`noRawBelowB_sound`); the premises of `topShips_transport` are then evaluated on the design a real compile produced (Check8 SNAPSHOT8, `synth_hftPcieOutByte`'s own design), instead of being assumed.
What this does NOT supply: `TopShips p n X b raw D` itself for a non-leaf (the machine route with `insts ≠ []`: `LeafFacts` is leaf-only), the child packages, `hsrc` (`ExtStage` induction instead of `ExtStage … 0 = id`). -/
namespace Tools.ShippingFGCircuitS1iChild
open Lean Sparkle.Core Sparkle.Core.Domain Tools.ShippingGen2 Tools.ShippingGen5FG
abbrev Module := Sparkle.IR.AST.Module
open Sparkle.IR.AST Sparkle.IR.OptCheck Sparkle.IR.RefineCheck
open Tools.ShippingGen5DCEntryR (NoRawBelow resetNk_transport)
open Tools.ShippingGen5DCEntryD (PostEntry)
open Tools.ShippingHierOpen (bodyInstOuts stmtInstOuts)

/-- `bodyInstOuts` reads the oracle only at the instance targets of the body -/
theorem bodyInstOuts_congr {ch ch' : String → Option (Module × Sparkle.IR.Semantics.WEnv)} :
    ∀ l : List Stmt, (∀ mn iname conns, Stmt.inst mn iname conns ∈ l → ch' mn = ch mn) →
      bodyInstOuts ch' l = bodyInstOuts ch l := by
  intro l
  induction l with
  | nil => intros; rfl
  | cons st rest ih =>
    intro h
    have h1 : stmtInstOuts ch' st = stmtInstOuts ch st := by
      cases st with
      | inst mn iname conns =>
        simp only [stmtInstOuts, h mn iname conns (List.mem_cons_self ..)]
      | _ => rfl
    unfold bodyInstOuts
    rw [h1, ih (fun mn iname conns hm => h mn iname conns (List.mem_cons_of_mem _ hm))]

/-- **`TopShips` moves from the core design to the printed design for a module with instances**, under `NoRawBelow` -/
theorem topShips_transport {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) (n : Nat) (X : Name) {b raw : Module}
    {D D' : Design} (hpe : PostEntry b raw D D')
    (hnoRaw : NoRawBelow D raw.name (n + 1) raw)
    (hnoOpt : NoRawBelow D raw.name (n + 1) (checkedOptimize b))
    (hnoB : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body → mn ≠ raw.name) :
    TopShips p n X b raw D → TopShips p n X b raw D' := by
  have hlk : ∀ mn : String, mn ≠ raw.name →
      Sparkle.IR.Machine.moduleByName D'.modules mn = Sparkle.IR.Machine.moduleByName D.modules mn :=
    fun mn hne => (Tools.ShippingGen5DCEntryN.postEntry_lookup_ne hpe hne).1
  rintro ⟨ids, nd, len, cache, regs, rnd, rlen, H⟩
  refine ⟨ids, nd, len, cache, regs, rnd, rlen, ?_⟩
  intro i bools bits T ins st0 mems kids h1 h2 h3 h4 h5 h6 h7 h8
  have hbio : bodyInstOuts (Tools.ShippingMachineLinked.childMap D'.modules) b.body =
      bodyInstOuts (Tools.ShippingMachineLinked.childMap D.modules) b.body :=
    bodyInstOuts_congr _ (fun mn iname conns hm =>
      (Tools.ShippingGen5DCEntryN.postEntry_lookup_ne hpe (hnoB mn iname conns hm)).2)
  obtain ⟨envsO, hrun, hlen, hobs⟩ := H i bools bits T ins st0 mems kids h1 h2 h3 h4 h5
    ((resetNk_transport hpe n kids hnoRaw).mpr h6) h7
    (fun x hx hx' => h8 x hx (by rw [hbio]; exact hx'))
  refine ⟨envsO, ?_, hlen, hobs⟩
  rw [Tools.ShippingGen5DCEntryT.runModuleTG_transport hlk n _ _ _ T _ hnoOpt]
  exact hrun

/-- `DesignTransport` in the shape of the endpoint theorems, for a module with instances -/
theorem designTransport_of_noRawBelow {ι : Type} {dom : ι → DomainConfig} (p : Pkg ι dom) {b raw : Module}
    {D D' : Design} (hpe : PostEntry b raw D D')
    (hnoRaw : ∀ n, NoRawBelow D raw.name (n + 1) raw)
    (hnoOpt : ∀ n, NoRawBelow D raw.name (n + 1) (checkedOptimize b))
    (hnoB : ∀ mn iname conns, Stmt.inst mn iname conns ∈ b.body → mn ≠ raw.name) :
    Tools.ShippingFGCircuitBridge.DesignTransport p p.decl b raw D D' :=
  fun n => topShips_transport p n p.decl hpe (hnoRaw n) (hnoOpt n) hnoB

/-! ## a computable checker for `NoRawBelow` -/

/-- no instance statement of the module (nor, to depth `k`, of the modules it instantiates in `D`) names the module `rn` -/
def noRawBelowB (D : Design) (rn : String) : Nat → Module → Bool
  | 0, _ => true
  | k + 1, mc =>
    mc.body.all fun st =>
      match st with
      | .inst mn _ _ =>
        mn != rn && (match Sparkle.IR.Machine.moduleByName D.modules mn with
          | some mc' => noRawBelowB D rn k mc'
          | none => true)
      | _ => true

theorem noRawBelowB_sound (D : Design) (rn : String) :
    ∀ (k : Nat) (mc : Module), noRawBelowB D rn k mc = true → NoRawBelow D rn k mc := by
  intro k
  induction k with
  | zero => intros; trivial
  | succ k ih =>
    intro mc h
    unfold noRawBelowB at h
    rw [List.all_eq_true] at h
    refine ⟨fun mn iname conns hm => ?_, fun mn iname conns mc' hm hl => ?_⟩
    · have := h _ hm
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
      exact this.1
    · have := h _ hm
      simp only [Bool.and_eq_true] at this
      rw [hl] at this
      exact ih mc' this.2

/-- no instance of the body names `rn` -/
def instsNeB (rn : String) (body : List Stmt) : Bool :=
  body.all fun st => match st with
    | .inst mn _ _ => mn != rn
    | _ => true

theorem instsNeB_sound (rn : String) (body : List Stmt) (h : instsNeB rn body = true) :
    ∀ mn iname conns, Stmt.inst mn iname conns ∈ body → mn ≠ rn := by
  intro mn iname conns hm
  unfold instsNeB at h
  rw [List.all_eq_true] at h
  have := h _ hm
  simpa using this

end Tools.ShippingFGCircuitS1iChild

#print axioms Tools.ShippingFGCircuitS1iChild.topShips_transport
#print axioms Tools.ShippingFGCircuitS1iChild.designTransport_of_noRawBelow
#print axioms Tools.ShippingFGCircuitS1iChild.noRawBelowB_sound
#print axioms Tools.ShippingFGCircuitS1iChild.instsNeB_sound
