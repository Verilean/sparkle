import Tools.ShippingKidsResetSat
import Tools.ShippingMachineShipsDepth
set_option autoImplicit false
-- BUILT (unit SRM16): dev run a2 (exit 0); the final-SHA rebuild is in REPORT-SRM16.md.
-- SCOPE: an EXPLICIT constructed children state `resetKids D n raw` of depth `n` (every instance's registers at their first-register reset values, memories 0, recursively) and
-- `resetNk_resetKids`: it satisfies `ResetNk n raw D`, PROVIDED the structural facts below hold of the modules of the design.  The structural facts (`hIU`, `hAg`, `hRd`) are PREMISES; they are not proved here for any concrete design.
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingSrm16Reset
open Sparkle.IR.AST Sparkle.IR.Semantics
open Tools.ShippingHierStateG Tools.ShippingHierState
open Tools.ShippingKidsResetSat (regInitOf instModOf instModule regInitOf_cases regInitOf_of_mem instModOf_of_mem)
open Tools.ShippingMachineDepth (ResetN)

/-- The reset state of module `mc` at depth `n`: registers at the first register's reset value, memories `0`, and (above depth `0`) every instance name's state the reset state of the module of the
first instance of that name (`mc` itself if there is none). -/
def resetKT (D : Design) : (n : Nat) → Module → KT n
  | 0, mc => (⟨regInitOf mc.body, fun _ _ => 0⟩ : KidState)
  | n + 1, mc => (⟨regInitOf mc.body, fun _ _ => 0, fun i => resetKT D n ((instModule mc D i).getD mc)⟩ : KState (KT n))

/-- The children state of the source module `raw` at depth `n`. -/
def resetKids (D : Design) (n : Nat) (raw : Module) : String → KT n :=
  fun i => resetKT D n ((instModule raw D i).getD raw)

theorem mem_of_moduleByName {ms : List Module} {mn : String} {mc : Module}
    (h : Sparkle.IR.Machine.moduleByName ms mn = some mc) : mc ∈ ms :=
  List.mem_of_find?_eq_some h

theorem instModule_of_inst {m : Module} {D : Design} {mn i : String} {conns : List (String × Expr)} {mc : Module}
    (hIU : ∀ (mn1 : String) (c1 : List (String × Expr)), Stmt.inst mn1 i c1 ∈ m.body → mn1 = mn)
    (hi : Stmt.inst mn i conns ∈ m.body)
    (hmb : Sparkle.IR.Machine.moduleByName D.modules mn = some mc) : instModule m D i = some mc := by
  have h1 : instModOf m.body i = some mn := instModOf_of_mem i mn m.body hIU ⟨conns, hi⟩
  unfold instModule
  rw [h1]
  exact hmb

theorem resetN_resetKT (D : Design)
    (hIU : ∀ m ∈ D.modules, ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ m.body → Stmt.inst mn' i c' ∈ m.body → mn = mn')
    (hAg : ∀ m ∈ D.modules, ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
      Stmt.register r c rs inp init ∈ m.body → Stmt.register r c' rs' inp' init' ∈ m.body → init.toNat = init'.toNat)
    (hRd : ∀ m ∈ D.modules, ∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ m.body →
      ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ m.body → init'.toNat = 0) :
    ∀ (n : Nat) (mc : Module), mc ∈ D.modules → ResetN D n mc (resetKT D n mc) := by
  intro n
  induction n with
  | zero =>
    intro mc hmc
    refine ⟨?_, ?_, ?_, trivial⟩
    · intro r c rs inp init hr
      exact regInitOf_of_mem r init mc.body
        (fun c' rs' inp' init' hm' => hAg mc hmc r c' rs' inp' init' c rs inp init hm' hr) ⟨c, rs, inp, hr⟩
    · intro nm i; rfl
    · intro nm aw dw c wa wd we ra rd cr ew er hm
      show regInitOf mc.body rd = 0
      rcases regInitOf_cases rd mc.body with h0 | ⟨c', rs', inp', init', hr, he⟩
      · exact h0
      · rw [he]; exact hRd mc hmc nm aw dw c wa wd we ra rd cr ew er hm c' rs' inp' init' hr
  | succ k ih =>
    intro mc hmc
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r c rs inp init hr
      exact regInitOf_of_mem r init mc.body
        (fun c' rs' inp' init' hm' => hAg mc hmc r c' rs' inp' init' c rs inp init hm' hr) ⟨c, rs, inp, hr⟩
    · intro nm i; rfl
    · intro nm aw dw c wa wd we ra rd cr ew er hm
      show regInitOf mc.body rd = 0
      rcases regInitOf_cases rd mc.body with h0 | ⟨c', rs', inp', init', hr, he⟩
      · exact h0
      · rw [he]; exact hRd mc hmc nm aw dw c wa wd we ra rd cr ew er hm c' rs' inp' init' hr
    · intro mn iname conns mc' hi hmb
      have hs : instModule mc D iname = some mc' :=
        instModule_of_inst (fun mn1 c1 h1 => hIU mc hmc mn1 iname c1 mn conns h1 hi) hi hmb
      show ResetN D k mc' (resetKT D k ((instModule mc D iname).getD mc))
      rw [hs]
      exact ih mc' (mem_of_moduleByName hmb)

/-- **The constructed children state is a reset children state.**  Premises (structural, PREMISE, about the modules of the design `D` and the source module `raw`): instance names determine their module in `raw` and in every module of `D`
(`hIUraw`, `hIU`), same-name registers of a module of `D` agree on `init.toNat` (`hAg`), a register named like a memory's read register has `init.toNat = 0` (`hRd`). -/
theorem resetNk_resetKids (n : Nat) (raw : Module) (D : Design)
    (hIUraw : ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ raw.body → Stmt.inst mn' i c' ∈ raw.body → mn = mn')
    (hIU : ∀ m ∈ D.modules, ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ m.body → Stmt.inst mn' i c' ∈ m.body → mn = mn')
    (hAg : ∀ m ∈ D.modules, ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
      Stmt.register r c rs inp init ∈ m.body → Stmt.register r c' rs' inp' init' ∈ m.body → init.toNat = init'.toNat)
    (hRd : ∀ m ∈ D.modules, ∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ m.body →
      ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ m.body → init'.toNat = 0) :
    Tools.ShippingMachineShipsDepth.ResetNk n raw D (resetKids D n raw) := by
  intro iname mc ⟨conns, hi⟩ hmb
  have hs : instModule raw D iname = some mc :=
    instModule_of_inst (fun mn1 c1 h1 => hIUraw mn1 iname c1 mc.name conns h1 hi) hi hmb
  show ResetN D n mc (resetKT D n ((instModule raw D iname).getD raw))
  rw [hs]
  exact resetN_resetKT D hIU hAg hRd n mc (mem_of_moduleByName hmb)

end Tools.ShippingSrm16Reset
