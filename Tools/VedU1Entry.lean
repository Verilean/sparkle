import Lean
import Sparkle.Compiler.Elab
import Tools.VedU1Contract
import Tools.VedU1Lemmas
import Tools.VedStrictAudit

/-!
# U1 checked entry, minimal end-to-end slice (`#ved_u1 decl`)

Design: docs/VERIFY-ELAB-DEEP-U0U1-DESIGN-2026-11-08.md §10.  This file does
NOT import `Tools.DeepElab`, and nothing in `Sparkle/` is changed.

`vedU1Entry declName` (and the command `#ved_u1 declName`):

1. specialises leading implicit `DomainConfig` binders (written
   `{dom : DomainConfig}` or auto-bound) at `defaultDomain`
   (`specialiseDomain`; any other non-explicit binder is left and refused),
   reads the port table from the TYPE of that statement term
   (`readTableOfType`; `readTable` and `ved_table%` read an unspecialised
   constant as before) and REFUSES, before any synthesis, a declaration with
   more than one output projection (the synthesizer's multi-output port
   naming is not confirmed; the reviewer allows refusing it);
2. calls `synthesizeCombinational declName` exactly ONCE (the function
   `#synthesizeVerilog` calls; main has no inliner fuel guard) and keeps the
   returned `(m, design)`.  The guarantee is about that returned module, not
   the Verilog the command prints (`toVerilog (optimizeModule m)`);
3. registers `declName.ved_mod : Module := toExpr m` (and checks, by
   evaluating that closed term back and comparing with `m` by `DecidableEq`,
   that the term denotes the very value returned), the contract
   `declName.ved_contract := contractOf tbl ["out"] clkRst declName.ved_mod`
   and the output list `declName.ved_outs`;
4. builds the expected type `U1Stmt declName.ved_contract declName.ved_mod
   stmt` as an `Expr`, where `stmt` is the ORIGINAL constant `@declName`, or
   `@declName defaultDomain` when step 1 specialised it (then the theorem is
   about that specialisation, not about every domain of the polymorphic
   declaration; the OK line says "specialised at defaultDomain"), elaborates a generated
   proof script against it (errors are never turned into `sorry`), adds the
   theorem `declName.ved_u1` to the kernel synchronously with exactly that
   type, re-reads its stored type and compares it with the expected `Expr`;
5. runs `Tools.VedStrictAudit.strictAudit` (standard 3 axioms, reachable
   closure, theorem, no mvars) on it;
6. returns / prints `m` ONLY if 3–5 succeed.  There is no fallback, no
   trace-only path and no skipped replay.

What a failure leaves and how it is reported (exactly what the code does):

* `checkU1` takes `saveState` when IT starts, i.e. AFTER `synthesizeCombinational`.
  On a failure inside `checkU1` (including heartbeat / max-recursion
  exceptions, caught with `tryCatchRuntimeEx`) it restores that TermElabM
  state: the constants it added (`ved_mod`, `ved_contract`, `ved_outs`,
  `ved_u1`, and any declaration a failed kernel step left) and its messages go back to the
  state at the checker's start.  It does NOT claim to roll back anything
  synthesis did: the environment before `synthesizeCombinational`, `IO.Ref`s /
  caches, or files are not restored.
* Reported as `VED U1 REFUSED <decl> [<stage>]: …`: every exception that
  `vedU1Entry` catches, i.e. the stages `table`, `multi-output` (both before
  synthesis), `synthesis` (`synthesizeCombinational`),
  and inside `checkU1` the stages `table`, `multi-output` (of the statement's
  constant), `artifact`, `type`, `proof`, `kernel`,
  `audit`, plus `checker` for any other exception raised inside `checkU1`
  (e.g. an `addDecl` of a registered name failing, or a runtime limit).
  NOT in that form: interrupt exceptions (never caught by the elaborator),
  and heartbeat / max-recursion exceptions raised by `readTable`,
  or `synthesizeCombinational` before `checkU1` starts (the plain
  `try … catch` there does not catch runtime exceptions; they propagate as
  their own errors).

The proof script is UNTRUSTED (the kernel checks it).  This slice's script
covers register-free modules built from not/and/or/xor/add/sub/mux/slice and
two-field concatenation (lemmas in Tools/VedU1Lemmas.lean), and modules with
exactly one register whose current value is the output (a delay); it is not
complete for every circuit these operators can build; any other body makes the script fail,
and the entry then refuses (stage `proof`), it never accepts.  The general
proof generator is open (§10).

`checkU1` is the checker below the entry; it takes the module, the constant
used in the statement and the proof separately ONLY so that the controls in
`Tests/Ved/U1EntryCheck.lean` can inject a substituted declaration, a mutated
module, another declaration's proof, or a `native_decide` proof.  The entry
itself always passes the synthesized `m`, the declaration itself and the
generated script.
-/

namespace Tools.VedU1Entry

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract

/-! ## `ToExpr` for the IR (the closed term of the returned module) -/

deriving instance Lean.ToExpr for Sparkle.IR.Type.DimExpr
deriving instance Lean.ToExpr for Sparkle.IR.Type.HWType
deriving instance Lean.ToExpr for Sparkle.IR.Type.ResetKind
deriving instance Lean.ToExpr for Sparkle.IR.AST.Parameter
deriving instance Lean.ToExpr for Sparkle.IR.AST.Port
deriving instance Lean.ToExpr for Sparkle.IR.AST.Operator
deriving instance Lean.ToExpr for Sparkle.IR.AST.Expr
deriving instance Lean.ToExpr for Sparkle.IR.AST.Stmt
deriving instance Lean.ToExpr for Sparkle.IR.AST.Module

/-! ## Lemmas the generated proofs use -/

/-- Concatenation arithmetic: a low field that fits its width. -/
theorem or_mod (a b w n : Nat) (hn : 2 ^ w = n) : a <<< w ||| b % n = a * n + b % n := by
  subst hn
  rw [← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos w)), Nat.shiftLeft_eq]

/-- `OutputsOn c m b f` from a one-cycle step invariant `R` (stream time `s`,
register state `st`): `R` holds initially, and from any state satisfying it one
cycle of the arrangement `b` succeeds, every listed output equals the
declaration's value at `s`, and `R` holds at `s+1`.  `outs` is the contract's
output list (`hO`). -/
theorem outputs_of_step (c : Contract) (m : Module) (b : List Stmt) (f : c.table.Ty) (outs : List Port)
    (hO : c.outputs = outs)
    (R : (Nat → String → Nat) → Nat → (String → Nat) → Prop)
    (h0 : ∀ ins, InputsOk c m ins → R ins 0 (st0 c m))
    (hstep : ∀ ins, InputsOk c m ins → ∀ s st (mems : MEnv), R ins s st →
      ∃ envF nexts mems', stepModule (declWidth m) b (seedIn m ins s st) mems =
          some (envF, nexts, mems') ∧
        (∀ o ∈ outs, envF o.name = srcOf c f ins o.name s) ∧ R ins (s + 1) (applyNexts st nexts)) :
    OutputsOn c m b f := by
  subst hO
  intro ins hok K
  have key : ∀ k s (st : String → Nat) (mems : MEnv), s + k = K → R ins s st →
      ∃ envs, runModule (declWidth m) b (seedFwd m K ins) k st mems = some envs ∧
        ∀ i, i < k → ∀ o ∈ c.outputs, ∃ env, envs[i]? = some env ∧
          env o.name = srcOf c f ins o.name (s + i) := by
    intro k
    induction k with
    | zero => intro s st mems _ _; exact ⟨[], rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro s st mems hK hR
      have hseed : seedFwd m K ins k st = seedIn m ins s st := by
        have h := seedFwd_time m K ins (t := s) (by omega) st
        have hk : K - 1 - s = k := by omega
        rw [hk] at h; exact h
      obtain ⟨envF, nexts, mems', hst, hout, hR'⟩ := hstep ins hok s st mems hR
      obtain ⟨rest, hrun, hrest⟩ := ih (s + 1) (applyNexts st nexts) mems' (by omega) hR'
      refine ⟨envF :: rest, ?_, ?_⟩
      · rw [runModule_first, hseed, hst]
        show (runModule (declWidth m) b (seedFwd m K ins) k (applyNexts st nexts) mems').bind _ = _
        rw [hrun]; rfl
      · intro i hi o ho
        cases i with
        | zero => exact ⟨envF, rfl, by simpa using hout o ho⟩
        | succ i =>
          obtain ⟨env, he, hv⟩ := hrest i (by omega) o ho
          exact ⟨env, by simpa using he, by rw [hv]; congr 1; omega⟩
  obtain ⟨envs, hrun, hall⟩ := key K 0 (st0 c m) (fun _ _ => 0) (by omega) (h0 ins hok)
  exact ⟨envs, hrun, fun t ht o ho => by simpa using hall t ht o ho⟩

/-- Refutation from one concrete run: a well-ordered arrangement `b` of the
body, an input stream in range, a run of length `K` that `b` actually
produces, and a cycle `t < K` where an output port differs from the
declaration.  Used by the controls (all its
premises are closed computations, checked by `decide`/`rfl`). -/
theorem not_outputs_of_witness (c : Contract) (m : Module) (f : c.table.Ty)
    (b : List Stmt) (hb : Sparkle.IR.Reorder.isPermOf b m.body = true)
    (hwo : Sparkle.IR.Reorder.woCheck [] b = true)
    (ins : Nat → String → Nat) (hok : InputsOk c m ins) (K t : Nat) (ht : t < K)
    (o : Port) (ho : o ∈ c.outputs) (envs : List Env)
    (hrun : runModule (declWidth m) b (seedFwd m K ins) K (st0 c m) (fun _ _ => 0) = some envs)
    (env : Env) (he : envs[t]? = some env) (hne : env o.name ≠ srcOf c f ins o.name t) :
    ¬ OutputsStmt c m f := by
  intro h
  obtain ⟨envs', hrun', hall⟩ := h b (Sparkle.IR.Reorder.isPermOf_sound hb)
    (Sparkle.IR.Reorder.woCheck_sound _ _ hwo) ins hok K
  rw [hrun] at hrun'
  cases hrun'
  obtain ⟨env', he', hv⟩ := hall t ht o ho
  rw [he] at he'
  cases he'
  exact hne hv

theorem not_u1_of_not_outputs {c : Contract} {m : Module} {f : c.table.Ty}
    (h : ¬ OutputsStmt c m f) : ¬ U1Stmt c m f := fun hu => h hu.2.2.2.2

/-! ## The entry -/

open Lean Meta Elab Term

/-- The refusal every failing path throws. -/
def refuse {α} (decl : Name) (stage : String) (msg : MessageData) : MetaM α :=
  throwError m!"VED U1 REFUSED {decl} [{stage}]: {msg}"

/-- Registers of a body (output, clock, reset name). -/
def regPorts (m : Sparkle.IR.AST.Module) : List (String × String × String) :=
  (regsOf m.body).map fun r => (r.1, r.2.1, r.2.2.1)

/-- `(clock, reset)` as the module's registers use them (`none` without
registers).  `ShapeCore` then requires every register to use exactly these and
`m.inputs` to end with them; this only chooses the names to check. -/
def clkRstOf (m : Sparkle.IR.AST.Module) : Option (String × String) :=
  match regPorts m with
  | [] => none
  | (_, k, r) :: _ => some (k, r)

/-- `toExpr m` evaluated back to a `Module`. -/
unsafe def evalModuleImpl (e : Lean.Expr) : MetaM Sparkle.IR.AST.Module :=
  Meta.evalExpr Sparkle.IR.AST.Module (Lean.mkConst ``Sparkle.IR.AST.Module) e

@[implemented_by evalModuleImpl]
opaque evalModule (e : Lean.Expr) : MetaM Sparkle.IR.AST.Module

/-- Add a non-computable definition (no compilation: the kernel and the
proofs only need its value). -/
def addDefn (n : Name) (ty val : Lean.Expr) : MetaM Unit := do
  addDecl (.defnDecl (mkDefinitionValEx n [] ty val .abbrev .safe []))
  enableRealizationsForConst n

/-- Names of the constants the checker registers for one check. -/
structure Names where
  mod : Name
  contract : Name
  outs : Name
  /-- the checked well-ordered arrangement of the body (proof data only) -/
  body : Name
  thm : Name

def Names.ofBase (base : Name) : Names :=
  { mod := base ++ `ved_mod, contract := base ++ `ved_contract, outs := base ++ `ved_outs,
    body := base ++ `ved_body, thm := base ++ `ved_u1 }

/-- The generated (untrusted) proof script for `U1Stmt C M F`.  `reg?` is
the single register of the delay shape (name, width), `none` for a
register-free module. -/
def scriptFor (nm : Names) (F : Name) (nDom : Nat) (reg? : Option (String × Nat))
    (inNames : List String := []) (eqs : Bool := false) : TermElabM Syntax := do
  let C := mkCIdent nm.contract
  let M := mkCIdent nm.mod
  let O := mkCIdent nm.outs
  -- `f` is the statement's term (`@F defaultDomain …` when specialised),
  -- `fI` the constant itself for the simp sets
  let fI := mkCIdent F
  let mut f : Term := fI
  if nDom > 0 then
    f ← `(@$fI)
    for _ in [0:nDom] do f ← `($f Sparkle.Core.Domain.defaultDomain)
  let B := mkCIdent nm.body
  match reg? with
  | none =>
    -- the input domain closes what the rewriting leaves (`==` against constants,
    -- a table's mux chain): every data input generalised, the goal reverted to
    -- `∀ x₀, x₀ < 2^w₀ → … → G` and decided by the kernel
    let insI := mkIdent `ins
    let sI := mkIdent `s
    let hinI := mkIdent `hin
    let xs := (List.range inNames.length).map fun i => mkIdent (Name.mkSimple s!"x{i}")
    let hs := (List.range inNames.length).map fun i => mkIdent (Name.mkSimple s!"hx{i}")
    let mut dom : Array (TSyntax `tactic) := #[]
    if inNames.length == 1 then
      dom := dom.push (← `(tactic| generalize $insI $sI $(Syntax.mkStrLit inNames[0]!) = $(xs[0]!) at $hinI:ident ⊢))
      dom := dom.push (← `(tactic| revert $hinI:ident))
      dom := dom.push (← `(tactic| revert $(xs[0]!)))
    else if inNames.length > 1 then
      let k := inNames.length
      for i in [0:k] do
        let mut t : Term := hinI
        for _ in [0:i] do t ← `($t.2)
        if i + 1 < k then t ← `($t.1)
        dom := dom.push (← `(tactic| have $(hs[i]!):ident := $t))
      for (n, (x, h)) in inNames.zip (xs.zip hs) do
        dom := dom.push (← `(tactic| generalize $insI $sI $(Syntax.mkStrLit n) = $x at $h:ident ⊢))
      for (x, h) in (xs.zip hs).reverse do
        dom := dom.push (← `(tactic| revert $h:ident))
        dom := dom.push (← `(tactic| revert $x:ident))
    let domAll ← `(tactic| all_goals
      $dom*
      decide +kernel)
    -- a body with `==` goes straight to the input domain (the range tactics
    -- below only fail on it, after costly case splits)
    let tail : Array (TSyntax `tactic) ←
      if eqs then pure #[domAll] else pure #[
        ← `(tactic| try omega),
        -- a `mux`: both arms in range
        ← `(tactic| try (split <;> simp <;> omega)),
        -- a `concat`: fields in range
        ← `(tactic| try (rw [BitVec.toNat_append]; simp [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt $hinI.1, Nat.mod_eq_of_lt $hinI.2])),
        domAll]
    `(by
        have hord : OrderOk $M $B = true := by decide +kernel
        refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$B, hord⟩, ?_⟩
        apply outputs_of_order $B hord
        apply outputs_of_step $C $M $B $f $O (by decide +kernel) (fun _ _ _ => True)
        · intro _ _; trivial
        · intro $insI hok $sI st mems _
          have $hinI := hok.1 $sI
          simp [$C:ident, contractOf, Contract.dataInputs, $M:ident, declWidth] at $hinI:ident
          simp [stepModule, evalAssigns, regNexts, memNexts, Sparkle.IR.Semantics.evalExpr,
            Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go,
            widthOf, seedIn, applyNexts, $O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident,
            Signal.register, OTy.obs, PTy.obs, PTy.sig, mask, or_mod _ _ _ _ rfl,
            Nat.shiftRight_eq_div_pow, Tools.VedU1Lemmas.evalOp_not_lit, $hinI:ident,
            Tools.VedU1Lemmas.compl_val,
            Tools.VedU1Lemmas.evalOp_and_lit, Tools.VedU1Lemmas.evalOp_or_lit,
            Tools.VedU1Lemmas.evalOp_xor_lit, Tools.VedU1Lemmas.and_val,
            Tools.VedU1Lemmas.or_val, Tools.VedU1Lemmas.xor_val,
            Tools.VedU1Lemmas.evalOp_add_lit, Tools.VedU1Lemmas.add_val, BitVec.toNat_add,
            Tools.VedU1Lemmas.evalOp_sub_lit, Tools.VedU1Lemmas.sub_val, BitVec.toNat_sub,
            Tools.VedU1Lemmas.evalOp_mux_lit, Tools.VedU1Lemmas.mux_val,
            Tools.VedU1Lemmas.evalOp_eq_lit, Tools.VedU1Lemmas.pure_val,
            Seq.seq, Signal.seq, Signal.ap, BitVec.toNat_append,
            BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt, Functor.map, Signal.map, BitVec.toNat_not, BitVec.toNat_ofNat]
          skip
          $tail*
          skip)
  | some (r, w) =>
    let rS := Syntax.mkStrLit r
    let wS := Syntax.mkNumLit (toString w)
    `(by
        have hord : OrderOk $M $B = true := by decide +kernel
        refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ⟨$B, hord⟩, ?_⟩
        apply outputs_of_order $B hord
        apply outputs_of_step $C $M $B $f $O (by decide +kernel)
          (fun ins s st => st $rS = srcOf $C $f ins "out" s)
        · intro ins hok
          simp [st0, $C:ident, contractOf, regsOf, $M:ident, srcOf, applyIns, $fI:ident,
            Signal.register, OTy.obs, PTy.obs, PTy.sig, encodeInit, mask, declWidth]
        · intro ins hok s st mems hR
          have hin := hok.1 s
          have hrst := hok.2 s
          simp [$C:ident, contractOf, Contract.dataInputs, $M:ident, declWidth] at hin hrst
          simp [stepModule, evalAssigns, regNexts, memNexts, Sparkle.IR.Semantics.evalExpr,
            Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go,
            widthOf, seedIn, applyNexts, $O:ident, $M:ident, $B:ident, declWidth, srcOf, $C:ident, contractOf, applyIns, $fI:ident,
            Signal.register, OTy.obs, PTy.obs, PTy.sig, mask, hrst, or_mod _ _ _ _ rfl,
            Nat.shiftRight_eq_div_pow] at hR ⊢
          have hlt : st $rS < 2 ^ $wS := by rw [hR]; exact BitVec.isLt _
          refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
          try rw [← hR]
          simp
          try omega)

open Sparkle.IR.Reorder in
/-- A well-ordered arrangement of a body (untrusted proof data: `OrderOk`
checks it in the kernel).  Stable: repeatedly take the FIRST remaining
statement none of whose reads another remaining statement writes.  When no
such statement is left (a combinational cycle) the rest is appended in its
own order, and `OrderOk` then fails. -/
def orderBody (body : List Sparkle.IR.AST.Stmt) : List Sparkle.IR.AST.Stmt := Id.run do
  let mut rest := body
  let mut out : Array Sparkle.IR.AST.Stmt := #[]
  for _ in [0:body.length] do
    let ready := fun (s : Sparkle.IR.AST.Stmt) =>
      (stmtReads s).all (fun n => !(writesOf (rest.erase s)).contains n)
    match rest.find? ready with
    | some s => out := out.push s; rest := rest.erase s
    | none => break
  return out.toList ++ rest

/-- The shape the slice's script handles (else `proof` would fail anyway;
this only picks the script variant). -/
def regShape (m : Sparkle.IR.AST.Module) : Option (String × Nat) :=
  match regsOf m.body with
  | [(r, _, _, _)] => some (r, declWidth m r)
  | _ => none

/-- Does an expression use `Operator.eq`? (only picks the script variant) -/
partial def exprHasEq : Sparkle.IR.AST.Expr → Bool
  | .op .eq _ => true
  | .op _ args | .concat args => args.any exprHasEq
  | .slice e _ _ | .sliceDim e _ _ => exprHasEq e
  | .index a i => exprHasEq a || exprHasEq i
  | _ => false

def bodyHasEq (body : List Sparkle.IR.AST.Stmt) : Bool :=
  body.any fun | .assign _ e => exprHasEq e | _ => false

/-- A proof source for `checkU1`. -/
inductive ProofSrc
  /-- the generated script (the only source the entry uses) -/
  | generated
  /-- CONTROLS ONLY: an arbitrary term (another declaration's theorem, a
  `native_decide` proof, …) -/
  | term (stx : Syntax)
  /-- A generated script built AFTER the checker has registered the module,
  contract and outputs (`Names`), from the returned module itself.  Anything
  the builder adds to the environment (auxiliary definitions) is inside the
  checker's save/restore scope and is taken back on a refusal.  Used by
  another entry (Tools/VedU1Deep.lean); the builder is untrusted like the
  script. -/
  | built (mk : Names → Sparkle.IR.AST.Module → TermElabM Syntax)

/-- Is `e` already a `VED U1 REFUSED …` error? -/
def isRefusal (e : Exception) : MetaM Bool := do
  return (← e.toMessageData.toString).startsWith "VED U1 REFUSED"

/-- The checker under the entry.  `decl` names the refusal; `stmt` is the
term put into the statement (the entry: `decl` itself, or `@decl defaultDomain`); `m` is the module
(the entry: the value `synthesizeCombinational` returned).  Returns the theorem name.

`stmt` may be any closed term, but the GENERATED script (`.generated`) only
supports a constant applied to `defaultDomain` arguments: it reads
`stmt.getAppFn.constName!` and takes every argument (`getAppNumArgs`) to be a
domain.  Another `stmt` makes that script fail, so the entry refuses; it can
not be accepted, because the theorem is checked against the full expected
type by the kernel.

On a failure (any non-interrupt exception raised inside it, runtime limits
included) it restores the TermElabM state saved when IT started, which takes
back the constants and messages the checker added (nothing synthesis did
before the call is rolled back), and throws `VED U1 REFUSED <decl> [<stage>]`;
an exception not already in that form is reported at stage `checker`.

`checkU1` verifies "this `m` has this declaration's meaning": the contract
reads the module name from `m` and does not bind it to `stmt`, so a
same-meaning `m` with another module name may be proved with a NEW proof.
That the entry inspects and returns the `m` it received, unsubstituted, is a
property of `vedU1Entry`, not of this statement. -/
def checkU1E (decl : Name) (base : Name) (stmt : Lean.Expr) (m : Sparkle.IR.AST.Module) (proof : ProofSrc) :
    TermElabM Name := do
  let nm := Names.ofBase base
  let saved ← saveState
  tryCatchRuntimeEx (do
    -- the table, from the TYPE of the statement's term
    let tbl ← try readTableOfType decl (← inferType stmt) catch e => refuse decl "table" e.toMessageData
    unless tbl.out.flat.length == 1 do
      refuse decl "multi-output"
        m!"{tbl.out.flat.length} output projections; the synthesizer's multi-output port naming is unconfirmed, refused (v1: one output)"
    -- the closed term of `m`, checked to denote `m` itself
    let mE := toExpr m
    let back ← evalModule mE
    unless decide (back = m) do
      refuse decl "artifact" m!"toExpr of the returned module does not evaluate back to it"
    let modTy := Lean.mkConst ``Sparkle.IR.AST.Module
    addDefn nm.mod modTy mE
    let some (.defnInfo di) := (← getEnv).find? nm.mod | refuse decl "artifact" m!"{nm.mod} missing"
    unless di.value == mE do refuse decl "artifact" m!"{nm.mod} does not hold toExpr m"
    let clkRst := clkRstOf m
    let cE := mkAppN (Lean.mkConst ``contractOf)
      #[toExpr tbl, toExpr ["out"], toExpr clkRst, Lean.mkConst nm.mod]
    addDefn nm.contract (Lean.mkConst ``Contract) cE
    let c := contractOf tbl ["out"] clkRst m
    addDefn nm.outs (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Port))
      (toExpr c.outputs)
    -- the order-free meaning needs one well-ordered arrangement of the body
    let b0 := orderBody m.body
    unless OrderOk m b0 do
      refuse decl "order"
        m!"no arrangement of the body assigns every wire before it is read (combinational cycle, self-read, undriven net or duplicate update)"
    addDefn nm.body (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt))
      (toExpr b0)
    -- the full expected statement, with the ORIGINAL constant
    let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
    try check expected catch e => refuse decl "type" e.toMessageData
    unless ← isProp expected do refuse decl "type" m!"expected statement is not a Prop"
    -- elaborate the proof (errors are not turned into sorry)
    let inNames := (dataPortsOf m clkRst).map fun p => p.name
    let stx ← match proof with
      | .generated => scriptFor nm stmt.getAppFn.constName! stmt.getAppNumArgs (regShape m) inNames (bodyHasEq m.body)
      | .term s => pure s
      | .built mk => try mk nm m catch e => refuse decl "proof" e.toMessageData
    let errsBefore := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
    let pf ← try
        withoutErrToSorry do
          let e ← elabTermEnsuringType stx expected
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
      catch e => refuse decl "proof" e.toMessageData
    let errs := (← Core.getMessageLog).toList.filter (·.severity == .error)
    if errs.length != errsBefore then
      let first ← match errs.drop errsBefore with
        | msg :: _ => msg.data.toString
        | [] => pure ""
      refuse decl "proof" m!"errors were logged while elaborating the proof; first: {first}"
    if pf.hasMVar || pf.hasFVar then refuse decl "proof" m!"proof term is not closed"
    -- the kernel, synchronously, with EXACTLY the expected type
    try
      withOptions (fun o => o.setBool `Elab.async false) do
        addDecl (.thmDecl { name := nm.thm, levelParams := [], type := expected, value := pf })
    catch e => refuse decl "kernel" e.toMessageData
    let some (.thmInfo ti) := (← getEnv).find? nm.thm
      | refuse decl "kernel" m!"{nm.thm} is not a theorem in the environment"
    unless ti.type == expected do refuse decl "type" m!"stored type differs from the expected statement"
    -- strict audit (standard 3 axioms, reachable closure)
    try discard <| Tools.VedStrictAudit.strictAudit nm.thm
    catch e => refuse decl "audit" e.toMessageData
    return nm.thm) fun e => do
    saved.restore (restoreInfo := true)
    if ← isRefusal e then throw e
    refuse decl "checker" e.toMessageData

/-- `checkU1E` for a statement that is a plain constant. -/
def checkU1 (decl : Name) (base : Name) (stmtDecl : Name) (m : Sparkle.IR.AST.Module) (proof : ProofSrc) :
    TermElabM Name :=
  checkU1E decl base (Lean.mkConst stmtDecl) m proof

/-- The U1 entry: `synthesizeCombinational` ONCE, the full statement over the
returned module and the declaration itself, kernel, strict audit; `m` is
returned only on success.  Failures of the steps before `checkU1` are tagged
(`table`, `multi-output`, `inliner`, `synthesis`) but NOT rolled back (see the
module docstring: runtime-limit exceptions there are not caught). -/
def vedU1EntryS (declName : Name) : TermElabM (Sparkle.IR.AST.Module × Design × Name × Nat) := do
  -- leading `DomainConfig` binders are instantiated with `defaultDomain`
  -- (the statement is then about `@declName defaultDomain`, NOT the
  -- polymorphic declaration); anything else is left for the table to refuse
  let (stmt, nDom) ← try specialiseDomain declName catch e => refuse declName "table" e.toMessageData
  -- refuse multi-output from the TYPE before any synthesis
  let tbl ← try readTableOfType declName (← inferType stmt) catch e => refuse declName "table" e.toMessageData
  unless tbl.out.flat.length == 1 do
    refuse declName "multi-output"
      m!"{tbl.out.flat.length} output projections; the synthesizer's multi-output port naming is unconfirmed, refused (v1: one output)"
  let (m, d) ← try Sparkle.Compiler.Elab.synthesizeCombinational declName
    catch e => refuse declName "synthesis" e.toMessageData
  let thm ← checkU1E declName declName stmt m .generated
  return (m, d, thm, nDom)

def vedU1Entry (declName : Name) : TermElabM (Sparkle.IR.AST.Module × Design × Name) := do
  let (m, d, thm, _) ← vedU1EntryS declName
  return (m, d, thm)

/-- `#ved_u1 decl`: run the entry; on success print the theorem, its audit
and the returned module; otherwise the refusal error. -/
elab "#ved_u1 " id:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, _, thm, nDom) ← vedU1EntryS decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U1 OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\n{repr m}"

end Tools.VedU1Entry
