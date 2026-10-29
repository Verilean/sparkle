import Tools.ShippingMachineInstG
set_option autoImplicit false
-- Built: g3p7-b4ee77eb and again in g3pf3-a9c42458 (clean, exit 0); scripts/gen2/GPOST_FREEZE.md item P7.
-- SCOPE: PURE facts about the two closings. From a successful closing, every child's module is
-- instantiated in the closed body. This is NOT a check of either closing: it follows from how the
-- instance statements are built (`closeInsts_calls`, `closeInstsG_calls`), and from the closings'
-- resolution of a call's module by its name (`moduleByName_name`).
-- The premise `hlen : children.length = insts.length` is explicit: a child past `insts.length`
-- would join the design without an instance. Its run supplier is a separate item (P2).
-- No `sorry`, no `axiom`, no `native_decide`.
namespace Tools.ShippingGen2KidsInst
open Sparkle.IR.AST Sparkle.IR.Machine

/-- **P7, one-output closing.** Every child's module is instantiated in the closed body.
Call `k` of child `children[k]` is the statement `instStmt … mc m` with
`moduleByName d.modules children[k].1.name = some mc` (`closeInsts_calls`), whose module name is
`mc.name = children[k].1.name` (`moduleByName_name`). -/
theorem closeInsts_kids_inst {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInsts nIn kI n portNames insts children (m₀, d₀) = some (m, d))
    (hlen : children.length = insts.length) :
    ∀ y ∈ children, ∃ (i : String) (cs : List (String × Expr)), Stmt.inst y.1.name i cs ∈ m.body := by
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  have hki : k < insts.length := by rw [← hlen]; exact hk
  obtain ⟨args, child, mc, _, hchild, hmc, st, hst, hcs⟩ :=
    Tools.ShippingMachineInst.closeInsts_calls h k hki
  rw [List.getElem?_eq_getElem hk] at hchild
  have hyc : children[k] = child := Option.some.inj hchild
  have hmn : mc.name = child.1.name := Tools.ShippingMachineInst.moduleByName_name hmc
  obtain ⟨outW, argWs, outP, iname, hrest⟩ := hcs
  -- the tenth conjunct of `CallStmt`: the statement itself
  have hstE := hrest.2.2.2.2.2.2.2.2.2
  subst hstE
  rw [hmn, ← hyc] at hst
  exact ⟨iname, _, hst⟩

/-- **P7, general closing.** Every child's module is instantiated in the closed body.
Entry `k` is in a call group (`callGroups_ok` coverage, used by `closeInstsG_calls`), whose
statement `instStmtG … mc m` is in the closed body with `moduleByName d.modules child.1.name =
some mc` for a `child` of the same name as `children[k]` (the group key equality); its module
name is `mc.name = child.1.name` (`moduleByName_name`). -/
theorem closeInstsG_kids_inst {nIn kI n : Nat} {portNames : List String} {insts : List (List Nat)}
    {fields : List String}
    {children : List (Module × Design)} {m₀ : Module} {d₀ : Design} {m : Module} {d : Design}
    (h : closeInstsG nIn kI n portNames insts fields children (m₀, d₀) = some (m, d))
    (hlen : children.length = insts.length) :
    ∀ y ∈ children, ∃ (i : String) (cs : List (String × Expr)), Stmt.inst y.1.name i cs ∈ m.body := by
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  have hki : k < insts.length := by rw [← hlen]; exact hk
  obtain ⟨st, hst, args, outs, child, mc, hcs, hmc, _, _, hch⟩ :=
    Tools.ShippingMachineInstG.closeInstsG_calls h k hki
  rw [List.getElem?_eq_getElem hk, Option.map_some] at hch
  have hn : children[k].1.name = child.1.name := Option.some.inj hch
  have hmn : mc.name = child.1.name := Tools.ShippingMachineInst.moduleByName_name hmc
  obtain ⟨outWs, argWs, iname, hrest⟩ := hcs
  -- the twelfth conjunct of `CallStmtG`: the statement itself
  have hstE := hrest.2.2.2.2.2.2.2.2.2.2.2
  subst hstE
  rw [hmn, ← hn] at hst
  exact ⟨iname, _, hst⟩

end Tools.ShippingGen2KidsInst
