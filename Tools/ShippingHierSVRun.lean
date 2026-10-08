import Tools.ShippingHierOptRun
import Tools.ShippingHierSVSoundness

/-! # A module with stateful children, to its emitted Verilog

The emitted Verilog of an instance-bearing module is its continuous
assignments, registers and the instantiations of its children. The SV
semantics of one module (`runModuleSV`) is open: the wires the instances
drive are free. A stateful linked run of the module (`runModuleTG`, each
instance stepping its child) IS the open run seeded, at each cycle, with the
values the children drove (`linked_open_runG`), and the emitted-SV check
carries that open run to the emitted Verilog (`seq_run_to_svI`): the
module's emitted Verilog, with its instance outputs taken from its children,
runs to the linked run's environments (`linked_sv_run`). -/
namespace Tools.ShippingHierSVRun
open Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.OptCheck
open Sparkle.IR.RegDedup (declWidth)
open Tools.ShippingHierarchySoundness Tools.ShippingHierOpen Tools.ShippingHierStateG
open Tools.ShippingHierState Tools.ShippingHierOptLinked Tools.ShippingHierOptRun
open Tools.SVParser.EmitSem (seqCheck emitAssigns emitRegs emitMemWrites runModuleSV)
open Tools.ShippingSeqSVSoundness (seqNames)
open Tools.ShippingHierSVSoundness (seqStmtOkI seq_run_to_svI)

/-- The oracle seeding of a run: at cycle `k`, the instance-driven wires
carry `E k`. -/
def oracle (children : String → Option (Module × WEnv)) (body : List Stmt) (E : Nat → Env)
    (seed : Nat → (String → Nat) → Env) : Nat → (String → Nat) → Env :=
  fun k st => seedOuts children body (E k) (seed k st)

/-- **The linked run is the open run from its oracle seeding.** -/
theorem linked_open_runG {σ : Type} (KS : KStep σ) (W : WEnv)
    (children : String → Option (Module × WEnv)) (body : List Stmt)
    (seed : Nat → (String → Nat) → Env) (E : Nat → Env)
    (hwf : linkedWF children body = true) :
    ∀ (T : Nat) (s : KState σ) (envs : List Env),
      runModuleTG KS W children body seed T s = some envs →
      (∀ j (hj : j < envs.length), envs[j] = E (T - 1 - j)) →
      runModule W body (oracle children body E seed) T s.st s.mems = some envs
  | 0, s, envs, h, _ => by simpa [runModuleTG, runModule] using h
  | k + 1, s, envs, h, hE => by
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
              have hE0 : envF' = E k := by
                have := hE 0 (by simp)
                simpa using this
              have hopen := linked_openKG KS W children s.kids s.mems body _ envF' s.kids kids'
                hwf hK
              have ih := linked_open_runG KS W children body seed E hwf k
                ⟨applyNexts s.st nexts, mems', kids'⟩ rest hR (fun j hj => by
                  have := hE (j + 1) (by simp; omega)
                  simp only [List.getElem_cons_succ] at this
                  rw [this]
                  congr 1
                  omega)
              have hopen' : evalAssigns W s.mems body (oracle children body E seed k s.st) =
                  some envF' := by
                simp only [oracle, ← hE0]; exact hopen
              simp only [runModule, stepModule, hopen', hN, hM, Option.bind_eq_bind,
                Option.bind_some]
              rw [ih]
              rfl

/-- **A module with stateful children, to its emitted Verilog.** A linked run
of `o` is the run of `o`'s emitted Verilog from the oracle seeding (its
instance outputs at each cycle the values its children drove), under the
emitted-SV check of `o` and its width agreement, when the oracle seeding
stays within the emitter's widths. -/
theorem linked_sv_run {σ : Type} (KS : KStep σ) (children : String → Option (Module × WEnv))
    {o : Module} {wof : String → Option Nat}
    (hwf : linkedWF children o.body = true)
    (hok : o.body.all seqStmtOkI = true)
    (hsv : seqCheck wof (Tools.SVParser.EmitSem.weOf wof) o.body = true)
    (hwag : ∀ n ∈ seqNames o.body, declWidth o n = Tools.SVParser.EmitSem.weOf wof n)
    {seed : Nat → (String → Nat) → Env} {T : Nat} {s : KState σ} {envs : List Env}
    (hrun : runModuleTG KS (declWidth o) children o.body seed T s = some envs)
    (hseedB : ∀ k st, Bounded (Tools.SVParser.EmitSem.weOf wof) st →
      Bounded (Tools.SVParser.EmitSem.weOf wof)
        (oracle children o.body (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) seed k st))
    (hst : Bounded (Tools.SVParser.EmitSem.weOf wof) s.st) :
    ∃ pairs regs mprog,
      emitAssigns wof o.body = some pairs ∧ emitRegs wof o.body = some regs ∧
      emitMemWrites wof o.body = some mprog ∧
      runModuleSV wof pairs regs mprog
        (oracle children o.body (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) seed) T
        s.st s.mems = some envs := by
  have hlen := runModuleTG_length KS _ children o.body seed T s envs hrun
  have hE : ∀ j (hj : j < envs.length),
      envs[j] = (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) (T - 1 - j) := by
    intro j hj
    simp only
    rw [show T - 1 - (T - 1 - j) = j by omega]
    simp [hj]
  have hopen := linked_open_runG KS (declWidth o) children o.body seed
    (fun k => (envs[T - 1 - k]?).getD (fun _ => 0)) hwf T s envs hrun hE
  exact seq_run_to_svI hok hsv hwag _ hseedB hst hopen

end Tools.ShippingHierSVRun
