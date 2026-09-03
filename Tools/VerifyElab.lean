/-
  `#verify_elab f` — kernel-checked proof that the IR the elaborator
  produces for a `circuit do` definition computes the same cycle trace
  as the definition's own Signal semantics.

  This is the link the other verifiers do not touch: `#verify_emit`
  and `#verify_dsl_roundtrip` are IR↔IR congruences, while user proofs
  live on the Signal side.  The generated theorem is

      f_elab_trace : ∀ inputs t,
        f_irTrace inputs t = ((f inputs).val t).toNat

  where `f_irTrace` is the register-state recurrence the PROVEN IR
  semantics (`Sparkle.IR.Semantics.evalExpr`) induces on the elaborated
  module — so the statement lands on the same semantics the M0–M4
  certified-roundtrip stack starts from, giving (per instance)

      Signal semantics ≡ IR semantics ≡ emitted SystemVerilog.

  Prototype and tactic-recipe validation:
  `Tests/Verification/ElabTracePrototype.lean`.

  v1 scope: single module, exactly ONE register, output = that
  register, all inputs `BitVec`-typed signals.  Same interactive-run
  caveat as `#verify_eq` (docs/KnownIssues.md Issue 2).
-/

import Lean
import Sparkle.Compiler.Elab
import Sparkle.IR.Semantics
import Tools.SVParser.VerifyEmit

open Sparkle.Core Sparkle.Core.Signal in
section
open Sparkle.Core Sparkle.Core.Signal

/-! ## The generic decomposition layer (proven once)

`runCircuitH` hides its feedback loop in a local `let`, so nothing
about the loop's STATE is nameable from a `circuit do` definition —
which is exactly what a multi-register or comb-output trace theorem
must talk about (one register's next value can depend on another's
current one, so no self-contained recurrence exists for the output
alone).

The fix needs no extraction at all: `runCircuitH`'s loop body is a
CLOSED FORM in the circuit body, so naming it (`loopFOf`) and the
output projection (`outFOf`) makes `runCircuitH_eq` hold by `rfl`, and
one strong-induction lemma (`loop_trace`) reduces every per-circuit
trace proof to a single step obligation that sees the loop only
through an agreement hypothesis.  Validated by hand on a two-register
circuit in scratch before this was written. -/

/-- The loop body `runCircuitH` feeds to `Sparkle.Core.Signal.Signal.loop`, as a named
    closed form over the circuit body. -/
def loopFOf {dom : Sparkle.Core.Domain.DomainConfig} {αs : List Type} {ρ : Type}
    [HasDomain ρ dom] [HListWireable αs] [Inhabited (HList αs)]
    (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
            Circuit dom (Circuit.SigList dom αs) ρ) :
    Sparkle.Core.Signal.Signal dom (HList αs) → Sparkle.Core.Signal.Signal dom (HList αs) :=
  fun live =>
    packRegister αs inits
      (body (mkRegList live αs (fun s => s) (fun f => f))
        (mkHolds αs live)).snd

/-- The output projection, same decomposition. -/
def outFOf {dom : Sparkle.Core.Domain.DomainConfig} {αs : List Type} {ρ : Type}
    [HasDomain ρ dom] [HListWireable αs] [Inhabited (HList αs)]
    (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
            Circuit dom (Circuit.SigList dom αs) ρ)
    (L : Sparkle.Core.Signal.Signal dom (HList αs)) : ρ :=
  (body (mkRegList L αs (fun s => s) (fun f => f)) (mkHolds αs L)).fst

/-- `runCircuitH` IS the projection of the loop — definitionally. -/
theorem runCircuitH_eq {dom : Sparkle.Core.Domain.DomainConfig} {αs : List Type} {ρ : Type}
    [HasDomain ρ dom] [HListWireable αs] [Inhabited (HList αs)]
    (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
            Circuit dom (Circuit.SigList dom αs) ρ) :
    runCircuitH inits body
      = outFOf inits body (Sparkle.Core.Signal.Signal.loop (loopFOf inits body)) := rfl

/-- A struct-returning `circuit do` projects one field.  The loop's
    STATE (`loopFOf`, which reads only `.snd`) is independent of the
    body's result type, so a field projection `P` of the whole result
    equals the same projection applied to `outFOf`.  This reduces a
    struct-output trace to the single-`outFOf` form the bridge already
    handles: `P` is pushed onto the output projection, the loop is
    untouched.  (Definitional — `runCircuitH`'s state loop never
    mentions `ρ`.) -/
theorem runCircuitH_proj_eq {dom : Sparkle.Core.Domain.DomainConfig}
    {αs : List Type} {ρ σ : Type}
    [HasDomain ρ dom] [HListWireable αs] [Inhabited (HList αs)]
    (P : ρ → σ)
    (inits : HList αs)
    (body : RegList dom (HList αs) (Circuit.SigList dom αs) αs →
            Circuit dom (Circuit.SigList dom αs) ρ) :
    P (runCircuitH inits body)
      = P (outFOf inits body
          (Sparkle.Core.Signal.Signal.loop (loopFOf inits body))) := rfl

/-- The generic joint-trace lemma: ONE per-instance obligation
    (`hstep`), which sees the loop's guarded prefix only through the
    agreement hypothesis — exactly what the per-circuit recipe can
    discharge. -/
theorem loop_trace {dom : Sparkle.Core.Domain.DomainConfig} {α : Type} [Inhabited α]
    (F : Sparkle.Core.Signal.Signal dom α → Sparkle.Core.Signal.Signal dom α) (trace : Nat → α)
    (hstep : ∀ t (pre : Sparkle.Core.Signal.Signal dom α),
      (∀ i, i < t → pre.val i = trace i) →
      (F pre).val t = trace t) :
    ∀ t, (Sparkle.Core.Signal.Signal.loop F).val t = trace t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    show Sparkle.Core.Signal.Signal.loopGo F t = trace t
    rw [Sparkle.Core.Signal.Signal.loopGo_eq]
    exact hstep t _ (fun i hi => by simp [hi]; exact ih i hi)

/-- `simp` sees `Add.add` (the unfolded `HAdd` chain), not `x + y`;
    these restate the `toNat` lemmas at that head.  Proofs are the
    originals — the forms are definitionally equal. -/
theorem toNat_AddAdd {w : Nat} (x y : BitVec w) :
    (Add.add x y).toNat = (x.toNat + y.toNat) % 2 ^ w :=
  BitVec.toNat_add x y

theorem toNat_SubSub {w : Nat} (x y : BitVec w) :
    (Sub.sub x y).toNat = (2 ^ w - y.toNat + x.toNat) % 2 ^ w :=
  BitVec.toNat_sub x y

/-- Pointwise form, for `rw` (F and t unify from the goal). -/
theorem loop_trace_at {dom : Sparkle.Core.Domain.DomainConfig} {α : Type} [Inhabited α]
    (F : Sparkle.Core.Signal.Signal dom α → Sparkle.Core.Signal.Signal dom α) (trace : Nat → α)
    (hstep : ∀ t (pre : Sparkle.Core.Signal.Signal dom α),
      (∀ i, i < t → pre.val i = trace i) →
      (F pre).val t = trace t) (t : Nat) :
    (Sparkle.Core.Signal.Signal.loop F).val t = trace t :=
  loop_trace F trace hstep t

/-! `.val`-pushing lemmas: every Signal-level operator instance,
    pointwise.  The deep route's bridge uses these instead of
    unfolding the `H*` class projections — a global `HXor.hXor`
    unfold rewrites the BitVec level too, leaving the two sides of
    each goal in different head forms (`XorOp.xor` vs `^^^`) that
    blind both simp and bv_decide. -/
section
open Sparkle.Core.Domain Sparkle.Core.Signal

variable {dom : DomainConfig} {m n : Nat}

theorem sigval_add (a b : Signal dom (BitVec n)) (t : Nat) :
    (a + b).val t = a.val t + b.val t := rfl
theorem sigval_sub (a b : Signal dom (BitVec n)) (t : Nat) :
    (a - b).val t = a.val t - b.val t := rfl
theorem sigval_mul (a b : Signal dom (BitVec n)) (t : Nat) :
    (a * b).val t = a.val t * b.val t := rfl
theorem sigval_and (a b : Signal dom (BitVec n)) (t : Nat) :
    (a &&& b).val t = a.val t &&& b.val t := rfl
theorem sigval_or (a b : Signal dom (BitVec n)) (t : Nat) :
    (a ||| b).val t = a.val t ||| b.val t := rfl
theorem sigval_xor (a b : Signal dom (BitVec n)) (t : Nat) :
    (a ^^^ b).val t = a.val t ^^^ b.val t := rfl
theorem sigval_shl (a b : Signal dom (BitVec n)) (t : Nat) :
    (a <<< b).val t = a.val t <<< b.val t := rfl
theorem sigval_shr (a b : Signal dom (BitVec n)) (t : Nat) :
    (a >>> b).val t = a.val t >>> b.val t := rfl
theorem sigval_append (a : Signal dom (BitVec m))
    (b : Signal dom (BitVec n)) (t : Nat) :
    (a ++ b).val t = a.val t ++ b.val t := rfl

theorem sigval_add_c (a : Signal dom (BitVec n)) (c : BitVec n)
    (t : Nat) : (a + c).val t = a.val t + c := rfl
theorem sigval_sub_c (a : Signal dom (BitVec n)) (c : BitVec n)
    (t : Nat) : (a - c).val t = a.val t - c := rfl
theorem sigval_mul_c (a : Signal dom (BitVec n)) (c : BitVec n)
    (t : Nat) : (a * c).val t = a.val t * c := rfl
theorem sigval_and_c (a : Signal dom (BitVec n)) (c : BitVec n)
    (t : Nat) : (a &&& c).val t = a.val t &&& c := rfl
theorem sigval_or_c (a : Signal dom (BitVec n)) (c : BitVec n)
    (t : Nat) : (a ||| c).val t = a.val t ||| c := rfl
theorem sigval_xor_c (a : Signal dom (BitVec n)) (c : BitVec n)
    (t : Nat) : (a ^^^ c).val t = a.val t ^^^ c := rfl
theorem sigval_shl_c (a : Signal dom (BitVec n)) (c : BitVec n)
    (t : Nat) : (a <<< c).val t = a.val t <<< c := rfl
theorem sigval_shr_c (a : Signal dom (BitVec n)) (c : BitVec n)
    (t : Nat) : (a >>> c).val t = a.val t >>> c := rfl
theorem sigval_append_c (a : Signal dom (BitVec m)) (c : BitVec n)
    (t : Nat) : (a ++ c).val t = a.val t ++ c := rfl

theorem sigval_c_add (c : BitVec n) (a : Signal dom (BitVec n))
    (t : Nat) : (c + a).val t = c + a.val t := rfl
theorem sigval_c_sub (c : BitVec n) (a : Signal dom (BitVec n))
    (t : Nat) : (c - a).val t = c - a.val t := rfl
theorem sigval_c_mul (c : BitVec n) (a : Signal dom (BitVec n))
    (t : Nat) : (c * a).val t = c * a.val t := rfl
theorem sigval_c_and (c : BitVec n) (a : Signal dom (BitVec n))
    (t : Nat) : (c &&& a).val t = c &&& a.val t := rfl
theorem sigval_c_or (c : BitVec n) (a : Signal dom (BitVec n))
    (t : Nat) : (c ||| a).val t = c ||| a.val t := rfl
theorem sigval_c_xor (c : BitVec n) (a : Signal dom (BitVec n))
    (t : Nat) : (c ^^^ a).val t = c ^^^ a.val t := rfl
theorem sigval_c_shl (c : BitVec n) (a : Signal dom (BitVec n))
    (t : Nat) : (c <<< a).val t = c <<< a.val t := rfl
theorem sigval_c_shr (c : BitVec n) (a : Signal dom (BitVec n))
    (t : Nat) : (c >>> a).val t = c >>> a.val t := rfl
theorem sigval_c_append (c : BitVec m) (a : Signal dom (BitVec n))
    (t : Nat) : (c ++ a).val t = c ++ a.val t := rfl

theorem sigval_and_b (a b : Signal dom Bool) (t : Nat) :
    (a &&& b).val t = (a.val t && b.val t) := rfl
theorem sigval_or_b (a b : Signal dom Bool) (t : Nat) :
    (a ||| b).val t = (a.val t || b.val t) := rfl
theorem sigval_xor_b (a b : Signal dom Bool) (t : Nat) :
    (a ^^^ b).val t = (a.val t ^^ b.val t) := rfl
theorem sigval_not (a : Signal dom (BitVec n)) (t : Nat) :
    (~~~a).val t = ~~~(a.val t) := rfl
theorem sigval_not_b (a : Signal dom Bool) (t : Nat) :
    (~~~a).val t = !(a.val t) := rfl
theorem sigval_neg (a : Signal dom (BitVec n)) (t : Nat) :
    (-a).val t = -(a.val t) := rfl
theorem sigval_mux {α} (c : Signal dom Bool) (a b : Signal dom α)
    (t : Nat) :
    (Sparkle.Core.Signal.Signal.mux c a b).val t
      = if c.val t then a.val t else b.val t := rfl
theorem sigval_beq {α} [BEq α] (a b : Signal dom α) (t : Nat) :
    (Sparkle.Core.Signal.Signal.beq a b).val t = (a.val t == b.val t) := rfl
theorem sigval_pure {α} (x : α) (t : Nat) :
    (Sparkle.Core.Signal.Signal.pure (dom := dom) x).val t = x := rfl

end

end

namespace Tools.VerifyElab

open Lean Elab Command
open Sparkle.IR.AST
open Sparkle.Core Sparkle.Core.Signal
open Sparkle.IR.Optimize (buildDefMap)
open Tools.SVParser.VerifyEmit (inlineCone widthTable denote varIdent)

deriving instance ToExpr for Sparkle.IR.Type.DimExpr
deriving instance ToExpr for Sparkle.IR.AST.Operator
deriving instance ToExpr for Sparkle.IR.AST.Expr

/-- The module's registers, in body order — which is the loop-state
    packing order (`packRegister` follows the HList left to right, and
    the elaborator emits registers as declared). -/
def theRegisters (m : Sparkle.IR.AST.Module) :
    List (String × Sparkle.IR.AST.Expr × Int) :=
  m.body.filterMap fun st => match st with
    | .register out _ _ input init => some (out, input, init)
    | _ => none

/-- Non-clock, non-reset inputs, elaborator order. -/
def dataInputs (m : Sparkle.IR.AST.Module) : List (String × Nat) :=
  m.inputs.filterMap fun p =>
    if p.name == "clk" || p.name == "rst" then none
    else some (p.name, p.ty.bitWidth)

/-- Right-nested tuple type of `n` copies of `Nat` (n ≥ 1). -/
def trTypeStx : Nat → CommandElabM Term
  | 0 => `(Unit)
  | 1 => `(Nat)
  | n+1 => do `(Nat × $(← trTypeStx n))

/-- Projection of component `i` out of `n` (right-nested tuple). -/
def projStx (s : Term) : Nat → Nat → CommandElabM Term
  | _, 0 => pure s
  | n, i+1 => do projStx (← `(($s).2)) (n-1) i

def projAt (s : Term) (n i : Nat) : CommandElabM Term := do
  let inner ← projStx s n i
  if i + 1 == n then pure inner else `(($inner).1)

/-- Resolve `slice (concat parts) hi lo` when the window falls exactly
    on one part — the shape inlining through the loop wire's register
    pack always produces.  Purely syntactic, part of goal generation
    (same trust shape as `inlineCone`): the generated cone must simply
    BE the register's input; without this, every cone that crosses the
    pack drags `<<< ||| >>>` arithmetic into all downstream goals.
    `wt` gives ref widths; the concat is MSB-first. -/
partial def resolveSlicesW (wt : Std.HashMap String Nat) :
    Sparkle.IR.AST.Expr → Sparkle.IR.AST.Expr
  | .slice (.concat parts0) hi lo => Id.run do
    -- flatten nested concats (the HList pack nests to the right)
    let rec flatten : Sparkle.IR.AST.Expr → List Sparkle.IR.AST.Expr
      | .concat ps => ps.flatMap flatten
      | e => [e]
    let parts := (parts0.flatMap flatten).map (resolveSlicesW wt)
    let widthOfPart : Sparkle.IR.AST.Expr → Option Nat := fun e =>
      match e with
      | .const _ w => some w
      | .ref n => wt.get? n
      | .slice _ h l => some (h - l + 1)
      | _ => none
    -- compute each part's [lo, hi] window (LSB-based, list is MSB-first)
    let some ws := parts.mapM widthOfPart | return .slice (.concat parts) hi lo
    let total := ws.foldl (· + ·) 0
    let mut acc := total
    for (p, w) in parts.zip ws do
      let pHi := acc - 1
      let pLo := acc - w
      if lo == pLo && hi == pHi then
        return p
      if pLo ≤ lo && hi ≤ pHi then
        return .slice p (hi - pLo) (lo - pLo)
      acc := acc - w
    return .slice (.concat parts) hi lo
  | .op o args => .op o (args.map (resolveSlicesW wt))
  | .concat args => .concat (args.map (resolveSlicesW wt))
  | .slice e hi lo =>
    match resolveSlicesW wt e with
    | .concat parts => resolveSlicesW wt (.slice (.concat parts) hi lo)
    | .ref n =>
      -- identity slice of a full-width ref collapses to the ref
      if lo == 0 && wt.get? n == some (hi + 1) then .ref n
      else .slice (.ref n) hi lo
    | .slice inner ihi _ilo =>
      -- slice-of-slice fusion: the OUTER window [hi,lo] is measured in
      -- the inner slice's bits, whose bit k is `inner`'s bit (ilo+k),
      -- so it re-slices `inner` at [ilo+hi, ilo+lo].  (ihi only bounds
      -- the inner width; the outer hi ≤ ihi-ilo already holds.)  Re-run
      -- to collapse the fused slice against `inner` (often a concat).
      let _ := ihi
      resolveSlicesW wt (.slice inner (_ilo + hi) (_ilo + lo))
    | e' => .slice e' hi lo
  | e => e

elab "#verify_elab" id:ident : command => do
  let declName ← liftTermElabM <|
    Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
  let design ← liftTermElabM
    (Sparkle.Compiler.Elab.synthesizeHierarchical declName)
  let m ← match design.modules with
    | [m] => pure m
    | _ => throwError "#verify_elab: single-module designs only"
  let regs := theRegisters m
  if regs.isEmpty then
    throwError "#verify_elab: no registers"
  let nRegs := regs.length
  let ins := dataInputs m
  let wt := widthTable m
  let regWs := regs.map fun (n, _, _) => wt.getD n 0
  -- inline every register's cone AND the output cone over
  -- {registers} ∪ inputs
  let stopAt : Std.HashMap String Bool :=
    (ins.foldl (fun (h : Std.HashMap String Bool) (n, _) =>
      h.insert n true) {})
    |> regs.foldl (fun h (n, _, _) => h.insert n true)
  let dm := buildDefMap m.body
  let cones ← regs.mapM fun (n, input, _) => do
    match inlineCone dm stopAt 10000 input with
    | .ok c => pure (n, resolveSlicesW wt c)
    | .error e => throwError "#verify_elab: cone of {n}: {e}"
  let outName ← match m.outputs with
    | [p] => pure p.name
    | _ => throwError "#verify_elab: exactly one output supported"
  let outCone ← match inlineCone dm stopAt 10000 (.ref outName) with
    | .ok c => pure (resolveSlicesW wt c)
    | .error e => throwError "#verify_elab: output cone: {e}"
  -- names
  let paramOf (n : String) : String :=
    match n.dropPrefix? "_gen_" with
    | some sub => sub.toString
    | none => n
  let base := declName.componentsRev.headD (Name.mkSimple "x")
    |>.toString
  let mkI (s : String) : Ident := mkIdent (Name.mkSimple s)
  let weId := mkI s!"{base}_weM"
  let envId := mkI s!"{base}_envAt"
  let trId := mkI s!"{base}_irTrace"
  let bndId := mkI s!"{base}_irTrace_bound"
  let thId := mkI s!"{base}_elab_trace"
  let paramIds : Array Ident :=
    (ins.map fun (n, _) => mkI (paramOf n)).toArray
  -- binder types come from the DSL function's OWN signature (a module
  -- input of width 1 may be `Signal … Bool`, not `Signal … (BitVec 1)`
  -- — guessing from the IR width generated ill-typed statements)
  let (paramTys, paramIsBool) ← liftTermElabM do
    let info ← getConstInfo declName
    Meta.forallTelescope info.type fun xs _ => do
      let mut tys : Array Term := #[]
      let mut bools : Array Bool := #[]
      for x in xs do
        let t ← Meta.inferType x
        tys := tys.push (← Lean.PrettyPrinter.delab t)
        bools := bools.push ((← Meta.whnf t).getAppArgs.any
          fun a => a.isConstOf ``Bool)
      pure (tys, bools)
  if paramTys.size != ins.length then
    throwError "#verify_elab: {paramTys.size} DSL parameters vs {ins.length} module inputs — unsupported shape"
  let paramBinders ← (paramIds.zip paramTys).mapM fun (pid, ty) => do
    `(Lean.Parser.Term.bracketedBinderF| ($pid : $ty))
  let appArgs : Array Term := paramIds.map fun p => ⟨p.raw⟩
  -- weM
  let weBody ← do
    let mut acc ← `((0 : Nat))
    for (n, w) in ((regs.map fun r => (r.1, wt.getD r.1 0)) ++ ins).reverse do
      acc ← `(if n == $(quote n) then $(quote w) else $acc)
    pure acc
  elabCommand (← `(def $weId : Sparkle.IR.Semantics.WEnv :=
    fun n => $weBody))
  -- cone constants
  let mut coneIds : Array Ident := #[]
  for (n, c) in cones do
    let cid := mkI s!"{base}_cone_{Sparkle.Backend.Verilog.sanitizeName n}"
    liftCoreM <| addAndCompile <| .defnDecl {
      name := cid.getId, levelParams := []
      type := mkConst ``Sparkle.IR.AST.Expr
      value := toExpr c, hints := .abbrev, safety := .safe }
    liftCoreM <| Lean.enableRealizationsForConst cid.getId
    coneIds := coneIds.push cid
  let outConeId := mkI s!"{base}_cone_out"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := outConeId.getId, levelParams := []
    type := mkConst ``Sparkle.IR.AST.Expr
    value := toExpr outCone, hints := .abbrev, safety := .safe }
  liftCoreM <| Lean.enableRealizationsForConst outConeId.getId
  -- envAt: registers ↦ projections of s, inputs ↦ toNat of signals
  let trTy ← trTypeStx nRegs
  let envBody ← do
    let mut acc ← `((0 : Nat))
    for i in (List.range ins.length).reverse do
      let (n, _) := ins[i]!
      let pid := mkI (paramOf n)
      let v ← if paramIsBool[i]! then
          `(if ($pid).val t then 1 else 0)
        else
          `((($pid).val t).toNat)
      acc ← `(if n == $(quote n) then $v else $acc)
    let sTerm : Term ← `(s)
    for i in (List.range nRegs).reverse do
      let (rn, _, _) := regs[i]!
      let pj ← projAt sTerm nRegs i
      acc ← `(if n == $(quote rn) then $pj else $acc)
    pure acc
  elabCommand (← `(def $envId $paramBinders* (s : $trTy) (t : Nat) :
      Sparkle.IR.Semantics.Env := fun n => $envBody))
  -- irTrace
  let initsTr ← do
    let comps := regs.map fun (_, _, init) => init.toNat
    let mut acc : Term ← `(($(quote comps.getLast!) : Nat))
    for c in comps.dropLast.reverse do
      acc ← `((($(quote c) : Nat), $acc))
    pure acc
  let stepTr ← do
    let mut comps : Array Term := #[]
    for cid in coneIds do
      comps := comps.push (← `((Sparkle.IR.Semantics.evalExpr $weId
        ($envId $appArgs* ($trId $appArgs* t) t) $cid).getD 0))
    let mut acc : Term := comps.back!
    for c in comps.pop.reverse do
      acc ← `(($c, $acc))
    pure acc
  elabCommand (← `(def $trId $paramBinders* : Nat → $trTy
    | 0 => $initsTr
    | t+1 => $stepTr))
  -- the bound: every component below its width
  let boundBody ← do
    let sTerm : Term ← `($trId $appArgs* t)
    let mut conjs : Array Term := #[]
    for i in List.range nRegs do
      let pj ← projAt sTerm nRegs i
      conjs := conjs.push (← `($pj < 2 ^ $(quote regWs[i]!)))
    let mut acc : Term := conjs.back!
    for c in conjs.pop.reverse do
      acc ← `($c ∧ $acc)
    pure acc
  elabCommand (← `(theorem $bndId $paramBinders* (t : Nat) :
      $boundBody := by
    induction t with
    | zero => simp [$trId:ident]
    | succ n ih =>
      simp only [$trId:ident]
      simp [$envId:ident, $weId:ident,
        Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList,
        Sparkle.IR.Semantics.evalOp, Sparkle.IR.Semantics.evalExpr.go,
        Sparkle.IR.Semantics.mask, Sparkle.IR.Semantics.widthOf,
        Sparkle.IR.Semantics.widthOf.go,
        $[$coneIds:ident],*]
      repeat' apply And.intro
      all_goals (repeat' split)
      all_goals (try simp_all)
      all_goals (first | omega | bv_omega)))
  -- the pack: fun (s : Nat) => the TRACE AT TIME s, components as
  -- BitVecs, HList-shaped (Unit tail).  The first generated version
  -- packed the time itself — `ofNat w s` — and every downstream goal
  -- quietly compared traces against the clock.
  let packBody ← do
    let sTerm : Term ← `($trId $appArgs* s)
    let mut acc : Term ← `(())
    for i in (List.range nRegs).reverse do
      let pj ← projAt sTerm nRegs i
      acc ← `((BitVec.ofNat $(quote regWs[i]!) $pj, $acc))
    pure acc
  -- the theorem
  elabCommand (← `(theorem $thId $paramBinders* (t : Nat) :
      (($(id) $appArgs*).val t).toNat
      = (Sparkle.IR.Semantics.evalExpr $weId
          ($envId $appArgs* ($trId $appArgs* t) t) $outConeId).getD 0
      := by
    have hbT := $bndId $appArgs* t
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
          bundle2,
          Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq,
          $trId:ident]
      | succ n =>
        have hb := $bndId $appArgs* n
        -- stage 1: the Signal side down to BitVec exprs over pack
        simp [loopFOf, packRegister, Signal.register, Circuit.next,
          Circuit.pure', Circuit.bind, mkHolds, Signal.map, Signal.mux,
          bundle2,
          Signal.pure, Functor.map, Seq.seq, Signal.ap, Signal.seq,
          hpre n (Nat.lt_succ_self n), HAdd.hAdd, HSub.hSub, HMul.hMul,
          HAnd.hAnd, HOr.hOr, HXor.hXor]
        -- stage 2: the IR side, from tr's evalExpr to arithmetic
        simp only [$trId:ident]
        simp [$envId:ident, $weId:ident,
          Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList,
          Sparkle.IR.Semantics.evalOp, Sparkle.IR.Semantics.evalExpr.go,
          Sparkle.IR.Semantics.mask, Sparkle.IR.Semantics.widthOf,
        Sparkle.IR.Semantics.widthOf.go,
          $[$coneIds:ident],*]
        -- stage 3: components, branches, arithmetic
        repeat' apply And.intro
        all_goals (repeat' split)
        all_goals (try simp_all [BitVec.toNat_eq, toNat_AddAdd,
          toNat_SubSub, BitVec.toNat_add,
          BitVec.extractLsb'_eq_extractLsb, BitVec.toNat_ofNat])
        all_goals (first | rfl | bv_decide | bv_omega)
    · simp [$envId:ident, $weId:ident, $outConeId:ident,
        Sparkle.IR.Semantics.evalExpr, Sparkle.IR.Semantics.evalList,
        Sparkle.IR.Semantics.evalOp, Sparkle.IR.Semantics.evalExpr.go,
        Sparkle.IR.Semantics.mask, Sparkle.IR.Semantics.widthOf,
        Sparkle.IR.Semantics.widthOf.go,
        BitVec.toNat_ofNat, BitVec.toNat_eq,
        BitVec.extractLsb'_eq_extractLsb]
      repeat' split
      all_goals (try simp_all)
      all_goals (first | rfl | bv_omega)))
  -- honesty check
  let axioms ← liftCoreM <| Lean.collectAxioms thId.getId
  if axioms.contains ``sorryAx then
    throwError "#verify_elab {declName}: a generated proof FAILED (the theorem depends on sorryAx) — see the errors above"
  logInfo m!"#verify_elab {declName}: PROVEN — {thId.getId} ({nRegs} registers, {ins.length} inputs; axioms clean)"

end Tools.VerifyElab
