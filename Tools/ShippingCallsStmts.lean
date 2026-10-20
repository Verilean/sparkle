import Tools.ShippingCallsParent

/-! # The instance statements of a real parent (one-output calls)

`instStmtsOf` succeeds — one statement per call, each the instance of the
call's child with its inputs connected to the call's argument `let` wires and
its output to the call's wire — from facts about the parent's ports (the
tail ports `ls`: the calls' outputs, the slots, the `let`s), the children
(`ChildComb`, as many inputs as the call has arguments, resolved by name to
themselves) and the closed module (the call's wire declared, the instance
name not a name of the module). Pure. -/
namespace Tools.ShippingCallsStmts
open Sparkle.IR.AST Sparkle.IR.Machine Sparkle.IR.Reorder
open Sparkle.IR.NameHints (Allocated)
open Tools.ShippingCloseInstsSome Tools.ShippingInstStmt Tools.ShippingGateChildComb
open Tools.ShippingCallsParent Tools.ShippingKidsComb

/-- An `Option` `mapM` succeeds where every element does, element by element. -/
theorem mapM_exists {α β : Type} (f : α → Option β) (Q : α → β → Prop) :
    ∀ (l : List α), (∀ a ∈ l, ∃ b, f a = some b ∧ Q a b) →
      ∃ r, l.mapM f = some r ∧ r.length = l.length ∧
        ∀ (i : Nat) (a : α) (b : β), l[i]? = some a → r[i]? = some b → Q a b
  | [], _ => ⟨[], rfl, rfl, fun i a b h => by simp at h⟩
  | a :: l, h => by
    obtain ⟨b, hb, hq⟩ := h a (List.mem_cons_self ..)
    obtain ⟨r, hr, hlen, hall⟩ := mapM_exists f Q l (fun x hx => h x (List.mem_cons_of_mem _ hx))
    refine ⟨b :: r, by simp only [List.mapM_cons, hb, hr, bind, Option.bind]; rfl,
      by simp [hlen], ?_⟩
    intro i a' b' ha hb'
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha hb'
      subst ha; subst hb'
      exact hq
    | succ i => exact hall i a' b' (by simpa using ha) (by simpa using hb')

/-- The argument wires of a call: the `let` ports its arguments name. -/
def argWsOf (ls : List Port) (kI n : Nat) (args : List Nat) : List String :=
  args.map fun a => ((ls[kI + n + a]?).map (·.name)).getD ""

/-- Statement `st` is call `k`'s instance. -/
def IsCall (ls : List Port) (kI n : Nat) (insts : List (List Nat))
    (children : List (Module × Design)) (k : Nat) (st : Stmt) : Prop :=
  ∃ (args : List Nat) (c : Module × Design) (outPort outP : Port),
    insts[k]? = some args ∧ children[k]? = some c ∧ ls[k]? = some outPort ∧
    c.1.outputs = [outP] ∧
    st = .inst c.1.name s!"inst{k}_{c.1.name}"
      (callConns c.1.inputs (argWsOf ls kI n args) outP outPort.name)

set_option maxHeartbeats 1000000 in
/-- **The instance statements of the calls.** -/
theorem instStmts_some {PI ls : List Port} {kI n K : Nat} {insts : List (List Nat)}
    {children : List (Module × Design)} {m : Module} {d : Design}
    (hkI : insts.length = kI) (hchL : children.length = kI)
    (hlsLen : ls.length = kI + n + K)
    (hlsNd : (ls.map (·.name)).Nodup)
    (hargsK : ∀ (k : Nat) (args : List Nat), insts[k]? = some args → ∀ a ∈ args, a < K)
    (hchild : ∀ (k : Nat) (c : Module × Design), children[k]? = some c → ChildComb c.1 ∧
      (∀ args : List Nat, insts[k]? = some args → c.1.inputs.length = args.length) ∧
      moduleByName (designWith children d).modules c.1.name = some c.1)
    (hwire : ∀ p ∈ ls, ∃ q ∈ m.wires, q.name = p.name)
    (hfresh : ∀ (k : Nat) (c : Module × Design), children[k]? = some c →
      s!"inst{k}_{c.1.name}" ∉
      m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.wires.map (·.name)) :
    ∃ stmts, instStmtsOf PI.length kI n ((PI ++ ls).map (·.name)) insts children m d = some stmts ∧
      stmts.length = kI ∧ (∀ k st, stmts[k]? = some st → IsCall ls kI n insts children k st) ∧
      ∃ outWs, outWsOf PI.length ((PI ++ ls).map (·.name)) insts = some outWs := by
  have hport : ∀ i, ((PI ++ ls).map (·.name))[PI.length + i]? = (ls[i]?).map (·.name) := by
    intro i
    rw [List.getElem?_map, List.getElem?_append_right (Nat.le_add_right _ _),
      Nat.add_sub_cancel_left]
  have hstep : ∀ k ∈ List.range insts.length, ∃ st,
      (do
        let args ← insts[k]?
        let child ← children[k]?
        let mc ← moduleByName (designWith children d).modules child.1.name
        instStmt PI.length kI n ((PI ++ ls).map (·.name)) k args mc m) = some st ∧
      IsCall ls kI n insts children k st := by
    intro k hk
    have hk' : k < kI := hkI ▸ List.mem_range.mp hk
    obtain ⟨args, hargs⟩ : ∃ args, insts[k]? = some args :=
      ⟨_, List.getElem?_eq_getElem (hkI ▸ hk')⟩
    obtain ⟨c, hc⟩ : ∃ c, children[k]? = some c := ⟨_, List.getElem?_eq_getElem (hchL ▸ hk')⟩
    obtain ⟨outPort, hop⟩ : ∃ p, ls[k]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hcomb, hfit, hres⟩ := hchild k c hc
    obtain ⟨ty, hout⟩ := hcomb.output
    have hargWs : args.mapM (fun j => ((PI ++ ls).map (·.name))[PI.length + kI + n + j]?) =
        some (argWsOf ls kI n args) := by
      refine mapM_some_of _ _ args (fun a ha => ?_)
      have hlt : kI + n + a < ls.length := by
        have := hargsK k args hargs a ha
        omega
      rw [show PI.length + kI + n + a = PI.length + (kI + n + a) by omega, hport,
        List.getElem?_eq_getElem hlt]
      rfl
    have hne : outPort.name ∉ argWsOf ls kI n args := by
      intro hmem
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hmem
      have hlt : kI + n + a < ls.length := by
        have := hargsK k args hargs a ha
        omega
      rw [List.getElem?_eq_getElem hlt] at he
      have := Tools.ShippingMachineCloses.nodup_index hlsNd (List.getElem?_eq_getElem hlt) hop
        (by simpa using he)
      omega
    have hinst := instStmt_some (nIn := PI.length) (kI := kI) (n := n) (k := k)
      (portNames := (PI ++ ls).map (·.name)) (args := args) (mc := c.1) (m := m)
      (outW := outPort.name) (argWs := argWsOf ls kI n args)
      (outP := { name := "out", ty := ty })
      (by rw [hport, hop]; rfl) hargWs
      (fun p hp => ⟨fun e => clk_not_allocated (e ▸ hcomb.inputAlloc p hp),
        fun e => Tools.ShippingRegisterSoundness.not_allocated_rst (e ▸ hcomb.inputAlloc p hp)⟩)
      (by rw [hfit args hargs]; simp [argWsOf])
      hcomb.inputNames hne hout
      (fun p hp e => out_not_allocated
        ((show p.name = "out" from e) ▸ hcomb.inputAlloc p hp))
      (show ("out" : String) ≠ "rst" by decide)
      (by
        obtain ⟨q, hq, hn⟩ := hwire outPort (List.mem_of_getElem? hop)
        exact ⟨q, hq, hn⟩)
      (hfresh k c hc)
    refine ⟨_, ?_, args, c, outPort, _, hargs, hc, hop, hout, rfl⟩
    simp only [hargs, hc, hres, bind, Option.bind]
    exact hinst
  obtain ⟨stmts, hst, hlen, hall⟩ := mapM_exists _ (IsCall ls kI n insts children)
    (List.range insts.length) hstep
  refine ⟨stmts, hst, by rw [hlen, List.length_range, hkI], ?_, ?_⟩
  · intro k st hk
    have hkl : k < insts.length := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      rw [hlen, List.length_range] at this
      exact this
    exact hall k k st (by rw [List.getElem?_range hkl]) hk
  · refine ⟨(List.range insts.length).map (fun k => ((ls[k]?).map (·.name)).getD ""), ?_⟩
    refine mapM_some_of _ _ _ (fun k hk => ?_)
    have hk' : k < ls.length := by
      have := List.mem_range.mp hk
      omega
    rw [hport, List.getElem?_eq_getElem hk']
    rfl

end Tools.ShippingCallsStmts
