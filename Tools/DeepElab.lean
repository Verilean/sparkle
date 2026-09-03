/-
  The GENERAL Signal↔IR theorem — the deep-embedding track (E0–E2).

  `#verify_elab` proves the Signal↔IR link per circuit, by generating a
  proof each time.  This file proves it ONCE, for every circuit in a
  closed deep grammar:

      CExpr Γ w      typed deep expressions (de Bruijn context Γ of
                     widths; const/var/add/sub/mux/eq in v0)
      Cdo Γr Γi w    a circuit: register inits, one next-state
                     expression per register, one output expression

  and four theorems, each a single induction / composition:

      CExpr.compile_correct   evalExpr (compile e) = (denote e).toNat
      Cdo.stateSig_eq         the Signal-level loop fixpoint equals the
                              spec recurrence  (via `loop_trace`, once)
      Cdo.irState_eq          the IR-side recurrence equals the spec
      Cdo.elab_general        the capstone: for EVERY deep circuit,
                              every input stream, every cycle, the
                              Signal output equals the compiled output
                              cone under the PROVEN `evalExpr`

  The only per-circuit obligation is injectivity of the slot names —
  decidable, discharged by `decide` on concrete circuits.

  What remains for full CompCert-shape (E3): reifying the `circuit do`
  surface syntax into `Cdo` values inside the macro, so user-written
  circuits are instances by construction; and growing the expression
  grammar op by op (each op = one constructor + three cases).  Circuits
  outside the grammar (e.g. arbitrary Lean functions under `.map`)
  keep the per-instance `#verify_elab` fallback.
-/

import Sparkle.IR.Semantics
import Tools.VerifyElab
open Sparkle.IR.AST Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.Core

/-! E0: typed deep expression embedding.  Context Γ = widths of the
    variables in scope (registers ++ inputs), de Bruijn indexed. -/

inductive CExpr : List Nat → Nat → Type where
  | const {Γ} (w : Nat) (v : Nat) : CExpr Γ w
  | var   {Γ} (i : Fin Γ.length) : CExpr Γ (Γ.get i)
  | add   {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | sub   {Γ w} (a b : CExpr Γ w) : CExpr Γ w
  | mux   {Γ w} (c : CExpr Γ 1) (t e : CExpr Γ w) : CExpr Γ w
  | eq    {Γ w} (a b : CExpr Γ w) : CExpr Γ 1

/-- Shallow denotation: BitVec values for the variables, BitVec out. -/
def CEnv (Γ : List Nat) := ∀ i : Fin Γ.length, BitVec (Γ.get i)

def CExpr.denote {Γ w} (ρ : CEnv Γ) : CExpr Γ w → BitVec w
  | .const _ v => BitVec.ofNat _ v
  | .var i => ρ i
  | .add a b => a.denote ρ + b.denote ρ
  | .sub a b => a.denote ρ - b.denote ρ
  | .mux c t e => if c.denote ρ = 1#1 then t.denote ρ else e.denote ρ
  | .eq a b => if a.denote ρ = b.denote ρ then 1#1 else 0#1

/-- Compilation to the IR, with a naming of the context slots. -/
def CExpr.compile {Γ w} (names : Fin Γ.length → String) :
    CExpr Γ w → Expr
  | .const w v => .const (Int.ofNat v) w
  | .var i => .ref (names i)
  | .add a b => .op .add [a.compile names, b.compile names]
  | .sub a b => .op .sub [a.compile names, b.compile names]
  | .mux c t e => .op .mux [c.compile names, t.compile names,
      e.compile names]
  | .eq a b => .op .eq [a.compile names, b.compile names]

/-- Compiled expressions carry their type-level width — the companion
    fact that pins `evalOp`'s node mask. -/
theorem CExpr.compile_width {Γ w} (names : Fin Γ.length → String)
    (we : WEnv) (hw : ∀ i, we (names i) = Γ.get i) :
    ∀ e : CExpr Γ w,
      Sparkle.IR.Semantics.widthOf we (e.compile names) = w := by
  intro e
  induction e with
  | const w v => simp [CExpr.compile, Sparkle.IR.Semantics.widthOf]
  | var i => simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, hw]
  | add a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha, ihb]
  | sub a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iha, ihb]
  | mux c t e ihc iht ihe =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf, iht, ihe]
  | eq a b iha ihb =>
    simp [CExpr.compile, Sparkle.IR.Semantics.widthOf]

/-- E1, THE general theorem: for any deep expression, the compiled IR
    under the PROVEN semantics computes the denotation — one structural
    induction, all circuits in the grammar at once. -/
theorem CExpr.compile_correct {Γ w} (names : Fin Γ.length → String)
    (we : WEnv) (env : Env) (ρ : CEnv Γ)
    (hw : ∀ i, we (names i) = Γ.get i)
    (hv : ∀ i : Fin Γ.length, env (names i) = (ρ i).toNat) :
    ∀ e : CExpr Γ w,
      evalExpr we env (e.compile names) = some (e.denote ρ).toNat := by
  intro e
  induction e with
  | const w v =>
    simp only [CExpr.compile, CExpr.denote, evalExpr, mask,
      BitVec.toNat_ofNat, Int.add_emod_right, ← Int.natCast_pow,
      ← Int.natCast_emod, Int.ofNat_eq_natCast, Int.toNat_natCast,
      Option.some_inj, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _)]
  | var i =>
    simp [CExpr.compile, CExpr.denote, evalExpr, hv]
  | add a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask, BitVec.toNat_add,
      CExpr.compile_width names we hw]
  | sub a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask, BitVec.toNat_sub,
      CExpr.compile_width names we hw, Nat.add_comm]
  | mux c t e ihc iht ihe =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      ihc, iht, ihe, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw]
    by_cases hc : denote ρ c = 1#1
    · simp [hc]
    · have h0 : (denote ρ c).toNat = 0 := by
        have hlt := (denote ρ c).isLt
        have h1 : (denote ρ c).toNat ≠ 1 := fun h =>
          hc (BitVec.eq_of_toNat_eq (by simpa using h))
        omega
      simp [hc, h0]
  | eq a b iha ihb =>
    simp [CExpr.compile, CExpr.denote, evalExpr, evalList, evalOp,
      iha, ihb, Sparkle.IR.Semantics.widthOf, mask,
      CExpr.compile_width names we hw]
    by_cases he : denote ρ a = denote ρ b
    · simp [he]
    · have hne : (denote ρ a).toNat ≠ (denote ρ b).toNat := fun h =>
        he (BitVec.eq_of_toNat_eq h)
      simp [he, hne]

/-! E2: the statement layer.  A deep circuit = register widths Γr,
    input widths Γi, one next-state expression per register, one
    output expression — all over the joined context Γr ++ Γi. -/

structure Cdo (Γr Γi : List Nat) (wOut : Nat) where
  inits : CEnv Γr
  next  : ∀ i : Fin Γr.length, CExpr (Γr ++ Γi) (Γr.get i)
  out   : CExpr (Γr ++ Γi) wOut

/-- Join a register valuation and an input valuation. -/
def CEnv.join {Γr Γi : List Nat} (ρr : CEnv Γr) (ρi : CEnv Γi) :
    CEnv (Γr ++ Γi) := fun i =>
  if h : i.val < Γr.length then
    have hw : (Γr ++ Γi).get i = Γr.get ⟨i.val, h⟩ :=
      List.getElem_append_left h
    hw ▸ ρr ⟨i.val, h⟩
  else
    have hj : i.val - Γr.length < Γi.length := by
      have := i.isLt; simp [List.length_append] at this; omega
    have hw : (Γr ++ Γi).get i = Γi.get ⟨i.val - Γr.length, hj⟩ := by
      simp [List.getElem_append_right (by omega : Γr.length ≤ i.val)]
    hw ▸ ρi ⟨i.val - Γr.length, hj⟩

/-- The Nat-level state recurrence (the SPEC side). -/
def Cdo.stateAt {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inp : Nat → CEnv Γi) : Nat → CEnv Γr
  | 0 => c.inits
  | t+1 => fun i =>
    (c.next i).denote (CEnv.join (c.stateAt inp t) (inp t))

/-- Output value at cycle t. -/
def Cdo.outAt {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inp : Nat → CEnv Γi) (t : Nat) : BitVec wOut :=
  c.out.denote (CEnv.join (c.stateAt inp t) (inp t))

/-! E2b: the Signal-level semantics of a `Cdo`, and the ONCE-proven
    bridge to the spec recurrence, via `loop_trace`. -/

instance {Γ : List Nat} : Inhabited (CEnv Γ) := ⟨fun _ => default⟩

variable {dom : Sparkle.Core.Domain.DomainConfig}

/-- The loop body: registers delay by one, next-state from the deep
    expressions over the previous state and the inputs. -/
def Cdo.loopF {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) :
    Sparkle.Core.Signal.Signal dom (CEnv Γr) →
    Sparkle.Core.Signal.Signal dom (CEnv Γr) :=
  fun live => ⟨fun t => match t with
    | 0 => c.inits
    | t+1 => fun i => (c.next i).denote
        (CEnv.join (live.val t) (fun j => (inpS j).val t))⟩

/-- Signal-level register state = the pure loop fixpoint. -/
def Cdo.stateSig {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) :
    Sparkle.Core.Signal.Signal dom (CEnv Γr) :=
  Sparkle.Core.Signal.Signal.loop (c.loopF inpS)

/-- ONCE: the Signal state equals the spec recurrence at every cycle. -/
theorem Cdo.stateSig_eq {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) (t : Nat) :
    (c.stateSig (dom := dom) inpS).val t
      = c.stateAt (fun t j => (inpS j).val t) t := by
  unfold Cdo.stateSig
  rw [loop_trace_at _ (fun s => c.stateAt (fun t j => (inpS j).val t) s)
    ?hstep]
  case hstep =>
    intro u pre hpre
    cases u with
    | zero => rfl
    | succ n =>
      show (fun i => (c.next i).denote
          (CEnv.join (pre.val n) (fun j => (inpS j).val n))) = _
      rw [hpre n (Nat.lt_succ_self n)]
      rfl

/-! E2a: compilation to the IR and the general spec↔IR theorem. -/

/-- A total map from names, built as an if-chain over an index list —
    the same shape `#verify_elab` generates.  Injectivity of `names`
    is a hypothesis here; concrete circuits discharge it by `decide`. -/
def chainMap {n : Nat} (names : Fin n → String) (val : Fin n → Nat) :
    List (Fin n) → String → Nat
  | [], _ => 0
  | i :: rest, s =>
    if names i == s then val i else chainMap names val rest s

theorem chainMap_lookup {n : Nat} (names : Fin n → String)
    (val : Fin n → Nat)
    (hinj : ∀ i j, names i = names j → i = j) :
    ∀ (l : List (Fin n)) (i : Fin n), i ∈ l →
      chainMap names val l (names i) = val i := by
  intro l
  induction l with
  | nil => intro i hi; simp at hi
  | cons j rest ih =>
    intro i hi
    by_cases hj : names j == names i
    · have : j = i := hinj _ _ (by simpa using hj)
      subst this
      simp [chainMap]
    · have hne : i ≠ j := fun h => by subst h; simp at hj
      simp only [chainMap, hj, if_neg (by simpa using hj)]
      exact ih i (by
        rcases List.mem_cons.mp hi with h | h
        · exact absurd h.symm (fun h => hne h.symm)
        · exact h)

/-- Width and value environments for a valuation over the context. -/
def weOfC {n : Nat} (names : Fin n → String) (Γget : Fin n → Nat) :
    WEnv := chainMap names Γget (List.finRange n)

def envOfC {n : Nat} (names : Fin n → String) (v : Fin n → Nat) :
    Env := chainMap names v (List.finRange n)

theorem weOfC_names {n} (names) (Γget : Fin n → Nat)
    (hinj : ∀ i j, names i = names j → i = j) (i : Fin n) :
    weOfC names Γget (names i) = Γget i :=
  chainMap_lookup names Γget hinj _ i (List.mem_finRange i)

theorem envOfC_names {n} (names) (v : Fin n → Nat)
    (hinj : ∀ i j, names i = names j → i = j) (i : Fin n) :
    envOfC names v (names i) = v i :=
  chainMap_lookup names v hinj _ i (List.mem_finRange i)

/-- `toNat` is invariant under width-cast. -/
theorem toNat_cast {a b : Nat} (h : a = b) (x : BitVec a) :
    (h ▸ x).toNat = x.toNat := by cases h; rfl

/-- The joined valuation at the Nat level. -/
def natJoin {Γr Γi : List Nat} (r : Fin Γr.length → Nat)
    (x : Fin Γi.length → Nat) : Fin (Γr ++ Γi).length → Nat := fun j =>
  if h : j.val < Γr.length then r ⟨j.val, h⟩
  else x ⟨j.val - Γr.length, by
    have := j.isLt; simp [List.length_append] at this; omega⟩

theorem natJoin_eq_join {Γr Γi : List Nat} (ρr : CEnv Γr) (ρi : CEnv Γi)
    (j : Fin (Γr ++ Γi).length) :
    natJoin (fun i => (ρr i).toNat) (fun i => (ρi i).toNat) j
      = (CEnv.join ρr ρi j).toNat := by
  unfold natJoin CEnv.join
  by_cases h : j.val < Γr.length <;> simp [h, toNat_cast]

/-- The IR-side state recurrence: each register's compiled cone under
    the PROVEN `evalExpr`, in the compiled module's environments. -/
def Cdo.irState {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (names : Fin (Γr ++ Γi).length → String)
    (inp : Nat → CEnv Γi) : Nat → Fin Γr.length → Nat
  | 0 => fun i => (c.inits i).toNat
  | t+1 => fun i =>
    (evalExpr (weOfC names (fun j => (Γr ++ Γi).get j))
      (envOfC names (natJoin (c.irState names inp t)
        (fun j => (inp t j).toNat)))
      ((c.next i).compile names)).getD 0

/-- **E2a, general**: the IR recurrence equals the spec, for EVERY deep
    circuit — one induction, `compile_correct` doing the per-register
    step. -/
theorem Cdo.irState_eq {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (names : Fin (Γr ++ Γi).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inp : Nat → CEnv Γi) (t : Nat) (i : Fin Γr.length) :
    c.irState names inp t i = (c.stateAt inp t i).toNat := by
  induction t generalizing i with
  | zero => rfl
  | succ n ih =>
    show (evalExpr _ _ ((c.next i).compile names)).getD 0 = _
    rw [CExpr.compile_correct names _ _
      (CEnv.join (c.stateAt inp n) (inp n))
      (fun j => weOfC_names names _ hinj j)
      (fun j => by
        rw [envOfC_names names _ hinj j, ← natJoin_eq_join]
        congr 1
        funext k
        exact ih k)]
    · rfl

/-- The Signal-level OUTPUT of a deep circuit. -/
def Cdo.outSig {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) :
    Sparkle.Core.Signal.Signal dom (BitVec wOut) :=
  ⟨fun t => c.out.denote
    (CEnv.join ((c.stateSig inpS).val t) (fun j => (inpS j).val t))⟩

/-- **THE GENERAL SIGNAL↔IR THEOREM (E2 capstone).**  For EVERY deep
    circuit, every input stream, and every cycle: the Signal-level
    output equals the compiled output cone under the PROVEN IR
    semantics, evaluated at the IR-side state recurrence.  One proof;
    no per-instance obligations beyond `decide`-able name injectivity. -/
theorem Cdo.elab_general {Γr Γi wOut} (c : Cdo Γr Γi wOut)
    (names : Fin (Γr ++ Γi).length → String)
    (hinj : ∀ i j, names i = names j → i = j)
    (inpS : ∀ j : Fin Γi.length,
      Sparkle.Core.Signal.Signal dom (BitVec (Γi.get j))) (t : Nat) :
    ((c.outSig (dom := dom) inpS).val t).toNat
      = (evalExpr (weOfC names (fun j => (Γr ++ Γi).get j))
          (envOfC names (natJoin
            (c.irState names (fun t j => (inpS j).val t) t)
            (fun j => ((inpS j).val t).toNat)))
          (c.out.compile names)).getD 0 := by
  rw [CExpr.compile_correct names _ _
    (CEnv.join (c.stateAt (fun t j => (inpS j).val t) t)
      (fun j => (inpS j).val t))
    (fun j => weOfC_names names _ hinj j)
    (fun j => by
      rw [envOfC_names names _ hinj j, ← natJoin_eq_join]
      congr 1
      funext k
      exact c.irState_eq names hinj _ t k)]
  show ((c.outSig (dom := dom) inpS).val t).toNat
      = (c.out.denote _).toNat
  unfold Cdo.outSig
  simp only [c.stateSig_eq inpS t]

/-! E3: reifying elaborated circuits into `Cdo` values.

The meta side lives here: turn an inlined IR cone back into a `CExpr`
term (well-defined on the compiler's image — the cones `#verify_elab`
already computes), so a circuit's deep value can be GENERATED and the
general theorem applied, leaving only the Signal-side bridge as a
per-instance proof. -/

namespace Tools.DeepElab

open Lean Elab Command

/-- Build the `CExpr Γ w` term for an inlined cone.  `slot` maps a ref
    name to its context index; widths are checked by the elaborator
    when the generated definition elaborates. -/
partial def toCExpr (slot : String → Option Nat) :
    Sparkle.IR.AST.Expr → CommandElabM Term
  | .const v w => do
    if v < 0 then throwError "#verify_elab_deep: negative const"
    `(CExpr.const $(quote w) $(quote v.toNat))
  | .ref n => do
    match slot n with
    | some i => `(CExpr.var ⟨$(quote i), by decide⟩)
    | none => throwError "#verify_elab_deep: unknown ref {n}"
  | .op .add [a, b] => do
    `(CExpr.add $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .sub [a, b] => do
    `(CExpr.sub $(← toCExpr slot a) $(← toCExpr slot b))
  | .op .mux [c, t, e] => do
    `(CExpr.mux $(← toCExpr slot c) $(← toCExpr slot t)
        $(← toCExpr slot e))
  | .op .eq [a, b] => do
    `(CExpr.eq $(← toCExpr slot a) $(← toCExpr slot b))
  | e => throwError "#verify_elab_deep: {repr e} outside the deep grammar"

end Tools.DeepElab

namespace Tools.DeepElab

open Lean Elab Command
open Tools.VerifyElab (theRegisters dataInputs resolveSlicesW)
open Tools.SVParser.VerifyEmit (inlineCone widthTable)
open Sparkle.IR.Optimize (buildDefMap)

/-- `#verify_elab_deep f` — reify `f`'s elaborated circuit into a deep
    `Cdo` value and certify it through the GENERAL theorem
    `Cdo.elab_general`.  The only per-circuit proof left is the
    Signal-side bridge (the validated recipe); everything about the IR
    is the one general theorem.  v0 scope: BitVec inputs. -/
elab "#verify_elab_deep" id:ident : command => do
  let declName ← liftTermElabM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  let design ← liftTermElabM
    (Sparkle.Compiler.Elab.synthesizeHierarchical declName)
  let m ← match design.modules with
    | [m] => pure m
    | _ => throwError "#verify_elab_deep: single-module designs only"
  let regs := theRegisters m
  let nR := regs.length
  if nR == 0 then throwError "#verify_elab_deep: no registers"
  let ins := dataInputs m
  let nI := ins.length
  let wt := widthTable m
  let regWs := regs.map fun (n, _, _) => wt.getD n 0
  let inWs := ins.map fun (_, w) => w
  let stopAt : Std.HashMap String Bool :=
    (ins.foldl (fun (h : Std.HashMap String Bool) (n, _) =>
      h.insert n true) {})
    |> regs.foldl (fun h (n, _, _) => h.insert n true)
  let dm := buildDefMap m.body
  let slotIdx : String → Option Nat := fun s =>
    match (regs.map (·.1)).idxOf? s with
    | some i => some i
    | none => (ins.map (·.1)).idxOf? s |>.map (· + nR)
  let cones ← regs.mapM fun (n, input, _) => do
    match inlineCone dm stopAt 10000 input with
    | .ok c => toCExpr slotIdx (resolveSlicesW wt c)
    | .error e => throwError "#verify_elab_deep: cone of {n}: {e}"
  let outName ← match m.outputs with
    | [p] => pure p.name
    | _ => throwError "#verify_elab_deep: exactly one output"
  let outC ← match inlineCone dm stopAt 10000 (.ref outName) with
    | .ok c => toCExpr slotIdx (resolveSlicesW wt c)
    | .error e => throwError "#verify_elab_deep: output cone: {e}"
  let wOut := wt.getD outName (m.outputs.head!.ty.bitWidth)
  -- names / syntax scaffolding
  let base := declName.componentsRev.headD (Name.mkSimple "x") |>.toString
  let mkI (s : String) : Ident := mkIdent (Name.mkSimple s)
  let deepId := mkI s!"{base}_deep"
  let nmId := mkI s!"{base}_nm"
  let thId := mkI s!"{base}_deep_trace"
  let regWsT : Array Term := regWs.toArray.map fun w => quote w
  let inWsT : Array Term := inWs.toArray.map fun w => quote w
  let ΓrT : Term ← `([$regWsT,*])
  let ΓiT : Term ← `([$inWsT,*])
  -- param binders from the DSL signature
  let paramOf (n : String) : String :=
    match n.dropPrefix? "_gen_" with
    | some sub => sub.toString | none => n
  let paramIds : Array Ident :=
    (ins.map fun (n, _) => mkI (paramOf n)).toArray
  let (paramTys, _) ← liftTermElabM do
    let info ← getConstInfo declName
    Lean.Meta.forallTelescope info.type fun xs _ => do
      let mut tys : Array Term := #[]
      for x in xs do
        tys := tys.push (← Lean.PrettyPrinter.delab (← Lean.Meta.inferType x))
      pure (tys, ())
  let paramBinders ← (paramIds.zip paramTys).mapM fun (pid, ty) => do
    `(Lean.Parser.Term.bracketedBinderF| ($pid : $ty))
  let appArgs : Array Term := paramIds.map fun p => ⟨p.raw⟩
  -- the deep value
  let initArms ← (List.range nR).toArray.mapM fun i => do
    let (_, _, init) := regs[i]!
    `(Lean.Parser.Term.matchAltExpr|
      | ⟨$(quote i), _⟩ => BitVec.ofNat _ $(quote init.toNat))
  let nextArms ← (List.range nR).toArray.mapM fun i => do
    `(Lean.Parser.Term.matchAltExpr|
      | ⟨$(quote i), _⟩ => $(cones[i]!))
  elabCommand (← `(def $deepId : Cdo $ΓrT $ΓiT $(quote wOut) where
    inits := fun i => match i with $initArms:matchAlt*
    next := fun i => match i with $nextArms:matchAlt*
    out := $outC))
  -- projection equations (rfl): rewrite `f_deep.next` etc. WITHOUT
  -- ever exposing the anonymous structure literal — a literal that
  -- appears in some hypotheses but not others (the pack references the
  -- NAME) leaves simp_all unable to see two forms of the same fact
  let nextEqId := mkI s!"{base}_deep_next"
  let initsEqId := mkI s!"{base}_deep_inits"
  let outEqId := mkI s!"{base}_deep_out"
  elabCommand (← `(theorem $nextEqId :
    Cdo.next $deepId = fun i => match i with $nextArms:matchAlt* := rfl))
  elabCommand (← `(theorem $initsEqId :
    Cdo.inits $deepId = fun i => match i with $initArms:matchAlt* := rfl))
  elabCommand (← `(theorem $outEqId : Cdo.out $deepId = $outC := rfl))
  -- slot names
  let nmArms ← (List.range (nR + nI)).toArray.mapM fun i => do
    let s := if h : i < nR then (regs[i]!).1 else (ins[i - nR]!).1
    `(Lean.Parser.Term.matchAltExpr| | ⟨$(quote i), _⟩ => $(quote s))
  elabCommand (← `(def $nmId :
      Fin (($ΓrT ++ $ΓiT : List Nat).length) → String := fun i =>
    match i with $nmArms:matchAlt*))
  -- the input family from the params
  let inpSArms ← (List.range nI).toArray.mapM fun j => do
    let pj : Ident := paramIds.getD j (mkI "unreachable")
    `(Lean.Parser.Term.matchAltExpr|
      | ⟨$(quote j), _⟩ => $pj)
  let inpS ← if nI == 0 then
      `((fun j => nomatch j :
        ∀ j : Fin ($ΓiT : List Nat).length,
          Sparkle.Core.Signal.Signal
            Sparkle.Core.Domain.defaultDomain
            (BitVec (($ΓiT : List Nat).get j))))
    else
      `((fun j => match j with $inpSArms:matchAlt* :
        ∀ j : Fin ($ΓiT : List Nat).length,
          Sparkle.Core.Signal.Signal
            Sparkle.Core.Domain.defaultDomain
            (BitVec (($ΓiT : List Nat).get j))))
  -- the pack: HList of stateAt components
  let packBody ← do
    let mut acc : Term ← `(())
    for i in (List.range nR).reverse do
      acc ← `((Cdo.stateAt $deepId
        (fun t j => (($inpS) j).val t) s ⟨$(quote i), by decide⟩, $acc))
    pure acc
  -- the theorem: general theorem + per-instance Signal bridge
  elabCommand (← `(theorem $thId $paramBinders* (t : Nat) :
      (($(id) $appArgs*).val t).toNat
      = (Sparkle.IR.Semantics.evalExpr
          (weOfC $nmId (fun j => (($ΓrT ++ $ΓiT : List Nat)).get j))
          (envOfC $nmId (natJoin
            (Cdo.irState $deepId $nmId (fun t j => (($inpS) j).val t) t)
            (fun j => ((($inpS) j).val t).toNat)))
          (CExpr.compile $nmId (Cdo.out $deepId))).getD 0 := by
    rw [← Cdo.elab_general $deepId $nmId (by decide) $inpS t]
    congr 1
    -- the Signal-side bridge: f's runCircuitH loop against the deep
    -- spec recurrence, both through loop_trace
    simp only [$id:ident]
    rw [runCircuitH_eq]
    simp only [outFOf, mkHolds, Signal.map]
    rw [loop_trace_at _ (fun s => $packBody) ?hstep]
    case hstep =>
      intro u pre hpre
      cases u with
      | zero =>
        simp [loopFOf, packRegister, Signal.register, Circuit.next,
          Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux,
          bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap,
          Signal.seq]
        simp [Cdo.stateAt, CExpr.denote, CEnv.join, toNat_cast,
          $nextEqId:ident, $initsEqId:ident]
      | succ n =>
        simp [loopFOf, packRegister, Signal.register, Circuit.next,
          Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux,
          bundle2, Signal.pure, Functor.map, Seq.seq, Signal.ap,
          Signal.seq, hpre n (Nat.lt_succ_self n), HAdd.hAdd, HSub.hSub,
          HMul.hMul, HAnd.hAnd, HOr.hOr, HXor.hXor]
        simp [Cdo.stateAt, CExpr.denote, CEnv.join, toNat_cast,
          $nextEqId:ident, $initsEqId:ident]
        repeat' apply And.intro
        all_goals (repeat' split)
        all_goals (try simp_all [BitVec.toNat_eq, toNat_AddAdd,
          toNat_SubSub, BitVec.toNat_add,
          BitVec.extractLsb'_eq_extractLsb, BitVec.toNat_ofNat])
        all_goals (first | rfl | bv_decide | (trace_state; bv_omega))
    · -- the output side: outSig against the packed projection
      simp only [Cdo.outSig]
      simp only [Cdo.stateSig_eq]
      simp [CExpr.denote, CEnv.join, Cdo.stateAt, toNat_cast,
        $nextEqId:ident, $initsEqId:ident, $outEqId:ident]
      repeat' split
      all_goals (try simp_all [BitVec.toNat_eq, BitVec.toNat_add,
        BitVec.toNat_ofNat])
      all_goals (first | rfl | bv_decide | bv_omega)))
  let axioms ← liftCoreM <| Lean.collectAxioms thId.getId
  if axioms.contains ``sorryAx then
    throwError "#verify_elab_deep {declName}: a generated proof FAILED (sorryAx) — see the errors above"
  logInfo m!"#verify_elab_deep {declName}: PROVEN via Cdo.elab_general — {thId.getId} ({nR} registers, {nI} inputs; axioms clean)"

end Tools.DeepElab
