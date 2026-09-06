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
import Tools.ConeFoldSlices

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

/-- A Bool register's HList slot is decoded from its `BitVec 1` state
    as `bif (x == 1#1) then 1#1 else 0#1`; that decode is the identity
    on a 1-bit value.  Closes the output/step goals where the packed
    Bool-register value meets its `BitVec 1` spec form. -/
theorem bif_beq_ofBool (x : BitVec 1) :
    (bif x == 1#1 then (1#1 : BitVec 1) else 0#1) = x := by
  bv_decide

theorem bif_beq_ofBool_toNat (x : BitVec 1) :
    (bif x == 1#1 then (1#1 : BitVec 1) else 0#1).toNat = x.toNat := by
  rw [bif_beq_ofBool]

/-- Bool-register NOT: `~~~` on the 1-bit state vs `!` on its Bool
    decode. -/
theorem beq_not_bv1 (x : BitVec 1) :
    (x == 1#1) = !(~~~x == 1#1) := by
  bv_decide

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
deriving instance ToExpr for Sparkle.IR.Type.ResetKind
deriving instance ToExpr for Sparkle.IR.AST.Stmt

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

set_option maxHeartbeats 1000000 in
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
    match Tools.ConeFold.inlineConeT dm stopAt 10000 input with
    | .ok c => pure (n, Tools.ConeFold.resolveSlicesT wt 10000 c, c)
    | .error e => throwError "#verify_elab: cone of {n}: {e}"
  let outName ← match m.outputs with
    | [p] => pure p.name
    | _ => throwError "#verify_elab: exactly one output supported"
  let (outCone, outConeRaw) ←
    match Tools.ConeFold.inlineConeT dm stopAt 10000 (.ref outName) with
    | .ok c => pure (Tools.ConeFold.resolveSlicesT wt 10000 c, c)
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
    for (n, w) in wt.toList do
      acc ← `(if n == $(quote n) then $(quote w) else $acc)
    pure acc
  elabCommand (← `(def $weId : Sparkle.IR.Semantics.WEnv :=
    fun n => $weBody))
  -- cone constants
  let mut coneIds : Array Ident := #[]
  let mut coneRawIds : Array Ident := #[]
  let mut regInIds : Array Ident := #[]
  for (n, c, craw) in cones do
    let cid := mkI s!"{base}_cone_{Sparkle.Backend.Verilog.sanitizeName n}"
    liftCoreM <| addAndCompile <| .defnDecl {
      name := cid.getId, levelParams := []
      type := mkConst ``Sparkle.IR.AST.Expr
      value := toExpr c, hints := .abbrev, safety := .safe }
    liftCoreM <| Lean.enableRealizationsForConst cid.getId
    coneIds := coneIds.push cid
    let crid := mkI s!"{base}_coneRaw_{Sparkle.Backend.Verilog.sanitizeName n}"
    liftCoreM <| addAndCompile <| .defnDecl {
      name := crid.getId, levelParams := []
      type := mkConst ``Sparkle.IR.AST.Expr
      value := toExpr craw, hints := .abbrev, safety := .safe }
    liftCoreM <| Lean.enableRealizationsForConst crid.getId
    coneRawIds := coneRawIds.push crid
  for (n, input, _) in regs do
    let rid := mkI s!"{base}_regIn_{Sparkle.Backend.Verilog.sanitizeName n}"
    liftCoreM <| addAndCompile <| .defnDecl {
      name := rid.getId, levelParams := []
      type := mkConst ``Sparkle.IR.AST.Expr
      value := toExpr input, hints := .abbrev, safety := .safe }
    liftCoreM <| Lean.enableRealizationsForConst rid.getId
    regInIds := regInIds.push rid
  let outConeId := mkI s!"{base}_cone_out"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := outConeId.getId, levelParams := []
    type := mkConst ``Sparkle.IR.AST.Expr
    value := toExpr outCone, hints := .abbrev, safety := .safe }
  liftCoreM <| Lean.enableRealizationsForConst outConeId.getId
  let outConeRawId := mkI s!"{base}_coneRaw_out"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := outConeRawId.getId, levelParams := []
    type := mkConst ``Sparkle.IR.AST.Expr
    value := toExpr outConeRaw, hints := .abbrev, safety := .safe }
  liftCoreM <| Lean.enableRealizationsForConst outConeRawId.getId
  -- per-instance seam constants: the module body, the stop set and the
  -- width table as OBJECT values, so the ConeFold bridge theorems'
  -- hypotheses become per-instance dischargeable facts about exactly
  -- the constants the goals mention (Tools/ConeFoldSlices.lean).
  -- The body is emitted TOPO-SORTED: the elaborator's raw body carries
  -- the loop-pack wire in source order (read before its assign), which
  -- is not well-ordered; the shipping emission pipeline sorts before
  -- emitting, and `evalAssigns`' in-order fold needs the same.  Cones
  -- are order-blind (buildDefMap is a map), so nothing else changes.
  let bodyId := mkI s!"{base}_body"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := bodyId.getId, levelParams := []
    type := mkApp (mkConst ``List [levelZero]) (mkConst ``Sparkle.IR.AST.Stmt)
    value := toExpr (Tools.SVParser.Lower.topoSortBody m.body),
    hints := .abbrev, safety := .safe }
  liftCoreM <| Lean.enableRealizationsForConst bodyId.getId
  let stopL : List String := (ins.map (·.1)) ++ (regs.map (·.1))
  let stopLId := mkI s!"{base}_stopL"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := stopLId.getId, levelParams := []
    type := mkApp (mkConst ``List [levelZero]) (mkConst ``String)
    value := toExpr stopL, hints := .abbrev, safety := .safe }
  liftCoreM <| Lean.enableRealizationsForConst stopLId.getId
  let wtLId := mkI s!"{base}_wtL"
  liftCoreM <| addAndCompile <| .defnDecl {
    name := wtLId.getId, levelParams := []
    type := mkApp (mkConst ``List [levelZero])
      (mkApp2 (mkConst ``Prod [levelZero, levelZero])
        (mkConst ``String) (mkConst ``Nat))
    value := toExpr wt.toList, hints := .abbrev, safety := .safe }
  liftCoreM <| Lean.enableRealizationsForConst wtLId.getId
  let stopAtMId := mkI s!"{base}_stopAtM"
  elabCommand (← `(def $stopAtMId : Std.HashMap String Bool :=
    ($stopLId).foldl (fun h n => h.insert n true) {}))
  let wtMId := mkI s!"{base}_wtM"
  elabCommand (← `(def $wtMId : Std.HashMap String Nat :=
    ($wtLId).foldl (fun m p => m.insert p.1 p.2) {}))
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
  -- THE SEAM, per instance (Tools/ConeFoldSlices.lean): the seed
  -- environment the recurrence evaluates cones in is width-bounded,
  -- and each register's cone evaluation equals the value the
  -- module-level combinational fold assigns to that register's input.
  -- Checker hypotheses and the inlining/resolution equations are
  -- discharged by native_decide (HashMap hashing is platform-opaque,
  -- so kernel `decide` cannot reduce them).
  let sbId := mkI s!"{base}_seed_bounded"
  elabCommand (← `(theorem $sbId $paramBinders* (t : Nat) :
      ∀ n, $envId $appArgs* ($trId $appArgs* t) t n
        < 2 ^ $weId n := by
    have hb := $bndId $appArgs* t
    intro n
    simp only [$envId:ident]
    repeat' split
    all_goals
      first
        | exact Nat.two_pow_pos _
        | (simp only [beq_iff_eq] at *
           subst_vars
           first
             | simpa [$weId:ident] using hb
             | (simp only [$weId:ident]
                first
                  | exact BitVec.isLt _
                  | (split <;> simp)
                  | (simp
                     first
                       | done
                       | exact BitVec.isLt _
                       | (split <;> simp)
                       | omega)
                  | omega)
             | (simp [$weId:ident]
                first
                  | done
                  | omega))))
  for i in List.range regs.length do
    let (rn, _, _) := regs[i]!
    let stepId := mkI s!"{base}_step_{Sparkle.Backend.Verilog.sanitizeName rn}"
    let cid := coneIds[i]!
    let crid := coneRawIds[i]!
    let rid := regInIds[i]!
    elabCommand (← `(theorem $stepId $paramBinders* (t : Nat)
        {env1 : Sparkle.IR.Semantics.Env} {v : Nat}
        (hrun : Sparkle.IR.Semantics.evalAssigns $weId (fun _ _ => 0)
          $bodyId ($envId $appArgs* ($trId $appArgs* t) t) = some env1)
        (hv : Sparkle.IR.Semantics.evalExpr $weId env1 $rid = some v) :
        Sparkle.IR.Semantics.evalExpr $weId
          ($envId $appArgs* ($trId $appArgs* t) t) $cid = some v := by
      have hres : $cid
          = Tools.ConeFold.resolveSlicesT $wtMId 10000 $crid := by
        native_decide
      rw [hres]
      exact Tools.ConeFold.cone_resolved_agrees_at_seed $weId
        (fun _ _ => 0) $stopAtMId $wtMId
        (Sparkle.IR.Reorder.woCheck_sound [] $bodyId (by native_decide))
        (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
        (Tools.ConeFold.noSelfReadCheck_sound _ (by native_decide))
        hrun
        (Tools.ConeFold.hwfCheck_sound $weId $stopAtMId $bodyId
          (by native_decide))
        (Tools.ConeFold.hwt_of_assoc $weId $wtLId (by native_decide))
        ($sbId $appArgs* t)
        (Tools.ConeFold.stopAtFrozenCheck_sound $stopAtMId $bodyId
          (by native_decide))
        (fuel := 10000) (e := $rid)
        (hinl := by native_decide)
        10000 hv))
  -- the REGISTER PHASE: regNexts' next-value list IS the recurrence's
  -- next state — the mask regNexts applies is killed by the
  -- recurrence's own bound AT t+1, and the reset wire reads 0 because
  -- the combinational fold never writes it.  v1 shape: every register
  -- input is a materialized wire (`.ref w`) — the elaborator always
  -- produces that; emission is skipped otherwise.
  let refWires? : Option (List String) := regs.foldr
    (fun (r : String × Sparkle.IR.AST.Expr × Int) acc =>
      match r.2.1, acc with
      | .ref w, some l => some (w :: l)
      | _, _ => none) (some [])
  let regRsts : List String := m.body.filterMap fun s =>
    match s with
    | .register _ _ (rstName, _) _ _ => some rstName
    | _ => none
  if let some regWires := refWires? then
    if regRsts.length == regs.length then
      let regstepId := mkI s!"{base}_regstep"
      let sTerm1 : Term ← `($trId $appArgs* (t + 1))
      let mut nextsItems : Array Term := #[]
      for i in List.range nRegs do
        let (rn, _, _) := regs[i]!
        let pj ← projAt sTerm1 nRegs i
        nextsItems := nextsItems.push (← `(($(quote rn), $pj)))
      let mut pre : Array (Lean.TSyntax `tactic) := #[]
      let mut finalArgs : Array Term := #[]
      for i in List.range nRegs do
        let (rn, _, _) := regs[i]!
        let rstName := regRsts[i]!
        let w := regWires[i]!
        let stepId := mkI s!"{base}_step_{Sparkle.Backend.Verilog.sanitizeName rn}"
        let rid := regInIds[i]!
        let hrstId := mkI s!"hrst{i}"
        let hstepId := mkI s!"hstep{i}"
        let hnextId := mkI s!"hnext{i}"
        let hbndId := mkI s!"hbnd{i}"
        let pj ← projAt sTerm1 nRegs i
        pre := pre.push (← `(tactic| have $hrstId:ident :
            env1 $(quote rstName) = 0 := by
          have hfr := Tools.ConeFold.evalAssigns_frame $weId (fun _ _ => 0)
            $bodyId _ env1 hrun
            (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
            $(quote rstName) (by native_decide)
          rw [hfr]
          simp [$envId:ident]))
        pre := pre.push (← `(tactic| have $hstepId:ident :=
          $stepId $appArgs* t hrun
            (show Sparkle.IR.Semantics.evalExpr $weId env1 $rid
                = some (env1 $(quote w)) by
              simp [$rid:ident, Sparkle.IR.Semantics.evalExpr])))
        pre := pre.push (← `(tactic| have $hnextId:ident :
            $pj = env1 $(quote w) := by
          simp only [$trId:ident]
          rw [$hstepId:ident]
          rfl))
        pre := pre.push (← `(tactic| have $hbndId:ident :
            env1 $(quote w) < 2 ^ $(quote regWs[i]!) := by
          rw [← $hnextId:ident]
          have hbb := $bndId $appArgs* (t + 1)
          omega))
        finalArgs := finalArgs.push (← `(Nat.mod_eq_of_lt $hbndId:ident))
        finalArgs := finalArgs.push (← `($hnextId:ident))
        finalArgs := finalArgs.push (← `($hrstId:ident))
      elabCommand (← `(theorem $regstepId $paramBinders* (t : Nat)
          {env1 : Sparkle.IR.Semantics.Env}
          (hrun : Sparkle.IR.Semantics.evalAssigns $weId (fun _ _ => 0)
            $bodyId ($envId $appArgs* ($trId $appArgs* t) t) = some env1) :
          Sparkle.IR.Semantics.regNexts $weId (fun _ _ => 0) $bodyId env1
            = some [$nextsItems,*] := by
        $[$pre:tactic]*
        simp only [$bodyId:ident, Sparkle.IR.Semantics.regNexts,
          Sparkle.IR.Semantics.evalExpr, Option.bind_eq_bind,
          Option.bind_some]
        simp [Sparkle.IR.Semantics.mask, $weId:ident, $[$finalArgs:term],*]))
      -- the CYCLE-LEVEL theorem: the stepModule iteration's register
      -- state IS the recurrence, for every cycle (induction; the
      -- register phase by {base}_regstep, the memory phase inert on a
      -- memory-free body, the seed matched to envAt by the invariant).
      let envStId := mkI s!"{base}_envSt"
      let st0Id := mkI s!"{base}_st0"
      let envStBody ← do
        let mut acc ← `((0 : Nat))
        for i in (List.range ins.length).reverse do
          let (n, _) := ins[i]!
          let pid := mkI (paramOf n)
          let v ← if paramIsBool[i]! then
              `(if ($pid).val t then 1 else 0)
            else
              `((($pid).val t).toNat)
          acc ← `(if n == $(quote n) then $v else $acc)
        for i in (List.range nRegs).reverse do
          let (rn, _, _) := regs[i]!
          acc ← `(if n == $(quote rn) then
            Sparkle.IR.Semantics.mask $(quote regWs[i]!) (st $(quote rn))
            else $acc)
        pure acc
      elabCommand (← `(def $envStId $paramBinders* (t : Nat)
          (st : String → Nat) : Sparkle.IR.Semantics.Env :=
        fun n => $envStBody))
      -- bounded for EVERY state (the register arms are masked), which
      -- is exactly the seed discipline the M4 capstone quantifies over
      let envStBndId := mkI s!"{base}_envSt_bounded"
      elabCommand (← `(theorem $envStBndId $paramBinders* (t : Nat)
          (st : String → Nat) :
          ∀ n, $envStId $appArgs* t st n < 2 ^ $weId n := by
        intro n
        simp only [$envStId:ident]
        repeat' split
        all_goals
          first
            | exact Nat.two_pow_pos _
            | (simp only [beq_iff_eq] at *
               subst_vars
               first
                 | (simp only [$weId:ident]
                    first
                      | exact Nat.mod_lt _ (Nat.two_pow_pos _)
                      | exact BitVec.isLt _
                      | (split <;> simp)
                      | (simp
                         first
                           | done
                           | exact Nat.mod_lt _ (Nat.two_pow_pos _)
                           | exact BitVec.isLt _
                           | (split <;> simp)
                           | omega)
                      | omega)
                 | (simp [$weId:ident]
                    first
                      | done
                      | omega))))
      let st0Body ← do
        let mut acc ← `((0 : Nat))
        for (rn, _, init) in regs.reverse do
          acc ← `(if n == $(quote rn) then $(quote init.toNat) else $acc)
        pure acc
      elabCommand (← `(def $st0Id : String → Nat := fun n => $st0Body))
      -- the width map in the Option form the M4 capstone consumes;
      -- defined as `some ∘ weM` so `weOf` collapses back to the
      -- generated width env DEFINITIONALLY (the capstone is ∀-wof, and
      -- the emitters only consult it at names the body mentions)
      let wofMId := mkI s!"{base}_wofM"
      elabCommand (← `(def $wofMId : String → Option Nat :=
        fun n => some ($weId n)))
      let weOfEqId := mkI s!"{base}_weOf_eq"
      elabCommand (← `(theorem $weOfEqId :
          Tools.SVParser.EmitSem.weOf $wofMId = $weId := rfl))
      let stateTraceId := mkI s!"{base}_state_trace"
      let stateConj ← do
        let sTerm : Term ← `($trId $appArgs* t)
        let mut conjs : Array Term := #[]
        for i in List.range nRegs do
          let (rn, _, _) := regs[i]!
          let pj ← projAt sTerm nRegs i
          conjs := conjs.push (← `(st $(quote rn) = $pj))
        let mut acc : Term := conjs.back!
        for c in conjs.pop.reverse do
          acc ← `($c ∧ $acc)
        pure acc
      elabCommand (← `(theorem $stateTraceId $paramBinders* :
          ∀ (t : Nat) {st : String → Nat},
          Tools.ConeFold.stepIter $weId $bodyId ($envStId $appArgs*)
            $st0Id t = some st → $stateConj := by
        intro t
        induction t with
        | zero =>
          intro st h
          simp only [Tools.ConeFold.stepIter, Option.some_inj] at h
          subst h
          simp [$st0Id:ident, $trId:ident]
        | succ t ih =>
          intro st' h
          simp only [Tools.ConeFold.stepIter, Option.bind_eq_bind] at h
          cases hprev : Tools.ConeFold.stepIter $weId $bodyId
              ($envStId $appArgs*) $st0Id t with
          | none => rw [hprev] at h; simp at h
          | some st =>
            rw [hprev] at h
            simp only [Option.bind_some] at h
            have ihc := ih hprev
            have henv : $envStId $appArgs* t st
                = $envId $appArgs* ($trId $appArgs* t) t := by
              have hbb := $bndId $appArgs* t
              funext n
              simp only [$envStId:ident, $envId:ident, ihc,
                Sparkle.IR.Semantics.mask]
              repeat' split
              all_goals first | rfl | omega
            rw [henv] at h
            simp only [Sparkle.IR.Semantics.stepModule,
              Option.bind_eq_bind] at h
            cases hrun : Sparkle.IR.Semantics.evalAssigns $weId
                (fun _ _ => 0) $bodyId
                ($envId $appArgs* ($trId $appArgs* t) t) with
            | none => rw [hrun] at h; simp at h
            | some env1 =>
              rw [hrun] at h
              simp only [Option.bind_some] at h
              rw [$regstepId $appArgs* t hrun] at h
              rw [Tools.ConeFold.memNexts_memFree $weId $bodyId
                (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))]
                at h
              simp only [Option.bind_some, Option.some_inj] at h
              subst h
              simp [Sparkle.IR.Semantics.applyNexts]))
  let stepOutId := mkI s!"{base}_step_out"
  elabCommand (← `(theorem $stepOutId $paramBinders* (t : Nat)
      {env1 : Sparkle.IR.Semantics.Env} {v : Nat}
      (hrun : Sparkle.IR.Semantics.evalAssigns $weId (fun _ _ => 0)
        $bodyId ($envId $appArgs* ($trId $appArgs* t) t) = some env1)
      (hv : Sparkle.IR.Semantics.evalExpr $weId env1
        (.ref $(quote outName)) = some v) :
      Sparkle.IR.Semantics.evalExpr $weId
        ($envId $appArgs* ($trId $appArgs* t) t) $outConeId = some v := by
    have hres : $outConeId
        = Tools.ConeFold.resolveSlicesT $wtMId 10000 $outConeRawId := by
      native_decide
    rw [hres]
    exact Tools.ConeFold.cone_resolved_agrees_at_seed $weId
      (fun _ _ => 0) $stopAtMId $wtMId
      (Sparkle.IR.Reorder.woCheck_sound [] $bodyId (by native_decide))
      (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
      (Tools.ConeFold.noSelfReadCheck_sound _ (by native_decide))
      hrun
      (Tools.ConeFold.hwfCheck_sound $weId $stopAtMId $bodyId
        (by native_decide))
      (Tools.ConeFold.hwt_of_assoc $weId $wtLId (by native_decide))
      ($sbId $appArgs* t)
      (Tools.ConeFold.stopAtFrozenCheck_sound $stopAtMId $bodyId
        (by native_decide))
      (fuel := 10000) (e := .ref $(quote outName))
      (hinl := by native_decide)
      10000 hv))
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
  -- the HEADLINE per-instance corollary (when the bridge lemmas were
  -- emitted): the DSL's Signal value at cycle t equals the module
  -- fold's OUTPUT WIRE under the iterated certified step semantics —
  -- Signal ≡ stepModule-iteration, every cycle.
  if refWires?.isSome && regRsts.length == regs.length then
    let envStId := mkI s!"{base}_envSt"
    let st0Id := mkI s!"{base}_st0"
    let stateTraceId := mkI s!"{base}_state_trace"
    let sigFoldId := mkI s!"{base}_signal_fold"
    elabCommand (← `(theorem $sigFoldId $paramBinders* (t : Nat)
        {st : String → Nat} {env1 : Sparkle.IR.Semantics.Env}
        (hstep : Tools.ConeFold.stepIter $weId $bodyId
          ($envStId $appArgs*) $st0Id t = some st)
        (hrun : Sparkle.IR.Semantics.evalAssigns $weId (fun _ _ => 0)
          $bodyId ($envStId $appArgs* t st) = some env1) :
        (($(id) $appArgs*).val t).toNat = env1 $(quote outName) := by
      have ihc := $stateTraceId $appArgs* t hstep
      have henv : $envStId $appArgs* t st
          = $envId $appArgs* ($trId $appArgs* t) t := by
        have hbb := $bndId $appArgs* t
        funext n
        simp only [$envStId:ident, $envId:ident, ihc,
          Sparkle.IR.Semantics.mask]
        repeat' split
        all_goals first | rfl | omega
      rw [henv] at hrun
      have hout := $stepOutId $appArgs* t hrun
        (show Sparkle.IR.Semantics.evalExpr $weId env1
            (.ref $(quote outName)) = some (env1 $(quote outName)) by
          simp [Sparkle.IR.Semantics.evalExpr])
      rw [$thId $appArgs* t, hout]
      rfl))
    -- and against runModule itself (the object the certified Arc-2
    -- capstones are stated over): the t-th trace entry's output wire
    -- is the Signal's value, for every cycle of a successful run.
    let sigRunId := mkI s!"{base}_signal_runModule"
    elabCommand (← `(theorem $sigRunId $paramBinders* (K : Nat)
        {envs : List Sparkle.IR.Semantics.Env}
        (hrunM : Sparkle.IR.Semantics.runModule $weId $bodyId
          (fun td s => $envStId $appArgs* (K - 1 - td) s) K $st0Id
          (fun _ _ => 0) = some envs) :
        ∀ t, t < K → ∃ env1, envs[t]? = some env1
          ∧ (($(id) $appArgs*).val t).toNat = env1 $(quote outName) := by
      intro t ht
      have hrunM' : Sparkle.IR.Semantics.runModule $weId $bodyId
          (fun td s => $envStId $appArgs* (0 + (K - 1 - td)) s) K $st0Id
          (fun _ _ => 0) = some envs := by
        rw [Tools.ConeFold.runModule_seed_congr $weId $bodyId K
          (fun td s => $envStId $appArgs* (0 + (K - 1 - td)) s)
          (fun td s => $envStId $appArgs* (K - 1 - td) s)
          (fun td htd => by simp only [Nat.zero_add])]
        exact hrunM
      obtain ⟨st', env1, hsi, hev, hget⟩ :=
        Tools.ConeFold.runModule_stepIter $weId $bodyId
          (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
          ($envStId $appArgs*) K 0 $st0Id envs hrunM' t ht
      refine ⟨env1, hget, ?_⟩
      have hsi' : Tools.ConeFold.stepIter $weId $bodyId
          ($envStId $appArgs*) $st0Id t = some st' := by
        rw [Tools.ConeFold.stepIter_seed_congr $weId $bodyId
          ($envStId $appArgs*)
          (fun tt s => $envStId $appArgs* (0 + tt) s) $st0Id t
          (fun tt htt => by simp only [Nat.zero_add])]
        exact hsi
      have hev' : Sparkle.IR.Semantics.evalAssigns $weId (fun _ _ => 0)
          $bodyId ($envStId $appArgs* t st') = some env1 := by
        have h0 : (0 : Nat) + t = t := by omega
        rw [← h0]
        exact hev
      exact $sigFoldId $appArgs* t hsi' hev'))
    -- UNCONDITIONAL form: the run itself always succeeds (evalOk —
    -- the body is memory-free with all-fragment RHSs, both decidable),
    -- so no `hrunM` hypothesis is needed.
    let sigRunU := mkI s!"{base}_signal_run"
    elabCommand (← `(theorem $sigRunU $paramBinders* (K : Nat) :
        ∃ envs, Sparkle.IR.Semantics.runModule $weId $bodyId
            (fun td s => $envStId $appArgs* (K - 1 - td) s) K $st0Id
            (fun _ _ => 0) = some envs
          ∧ ∀ t, t < K → ∃ env1, envs[t]? = some env1
            ∧ (($(id) $appArgs*).val t).toNat = env1 $(quote outName) := by
      obtain ⟨envs, henvs⟩ := Option.isSome_iff_exists.mp
        (Tools.ConeFold.runModule_isSome $weId $bodyId
          (Tools.ConeFold.memFreeCheck_sound _ (by native_decide))
          (by native_decide)
          (fun td s => $envStId $appArgs* (K - 1 - td) s) K $st0Id)
      exact ⟨envs, henvs, $sigRunId $appArgs* K henvs⟩))
    -- THE M4 COMPOSITION: Signal ≡ the VERILOG SEMANTICS of the
    -- certified twin emission (certified_forward_trace_module), for
    -- every cycle of a successful run.
    let wofMId := mkI s!"{base}_wofM"
    let weOfEqId := mkI s!"{base}_weOf_eq"
    let envStBndId := mkI s!"{base}_envSt_bounded"
    let sigSvId := mkI s!"{base}_signal_sv"
    elabCommand (← `(theorem $sigSvId $paramBinders* :
        ∃ pairs regs mprog,
        Tools.SVParser.EmitSem.emitAssigns $wofMId $bodyId = some pairs
        ∧ Tools.SVParser.EmitSem.emitRegs $wofMId $bodyId = some regs
        ∧ Tools.SVParser.EmitSem.emitMemWrites $wofMId $bodyId
            = some mprog
        ∧ ∀ (K : Nat) (envs : List Sparkle.IR.Semantics.Env),
            Tools.SVParser.EmitSem.runModuleSV $wofMId pairs regs mprog
              (fun td s => $envStId $appArgs* (K - 1 - td) s) K $st0Id
              (fun _ _ => 0) = some envs →
            ∀ t, t < K → ∃ env1, envs[t]? = some env1
              ∧ (($(id) $appArgs*).val t).toNat
                  = env1 $(quote outName) := by
      have hchk : Tools.SVParser.EmitSem.seqCheck $wofMId
          (Tools.SVParser.EmitSem.weOf $wofMId) $bodyId = true := by
        native_decide
      have hbnd : ∀ (K t : Nat) (st : String → Nat),
          Sparkle.IR.Semantics.Bounded
            (Tools.SVParser.EmitSem.weOf $wofMId)
            ($envStId $appArgs* (K - 1 - t) st) := by
        intro K t st
        rw [$weOfEqId:ident]
        exact $envStBndId $appArgs* (K - 1 - t) st
      obtain ⟨pairs, regs, mprog, h1, h2, h3, _⟩ :=
        Tools.SVParser.EmitSem.certified_forward_trace_module hchk
          (fun td s => $envStId $appArgs* (1 - 1 - td) s) (hbnd 1)
      refine ⟨pairs, regs, mprog, h1, h2, h3, ?_⟩
      intro K envs hSV t ht
      obtain ⟨pairs', regs', mprog', h1', h2', h3', heq⟩ :=
        Tools.SVParser.EmitSem.certified_forward_trace_module hchk
          (fun td s => $envStId $appArgs* (K - 1 - td) s) (hbnd K)
      rw [h1] at h1'
      rw [h2] at h2'
      rw [h3] at h3'
      cases h1'
      cases h2'
      cases h3'
      have hrunM := heq K $st0Id (fun _ _ => 0)
      rw [$weOfEqId:ident, hSV] at hrunM
      exact $sigRunId $appArgs* K hrunM t ht))
  -- honesty check
  let axioms ← liftCoreM <| Lean.collectAxioms thId.getId
  if axioms.contains ``sorryAx then
    throwError "#verify_elab {declName}: a generated proof FAILED (the theorem depends on sorryAx) — see the errors above"
  logInfo m!"#verify_elab {declName}: PROVEN — {thId.getId} ({nRegs} registers, {ins.length} inputs; axioms clean)"

end Tools.VerifyElab
