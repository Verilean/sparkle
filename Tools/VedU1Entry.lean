import Lean
import Sparkle.Compiler.Elab
import Tools.VedU1Contract
import Tools.VedU1Lemmas
import Tools.VedU1Table
import Tools.VedU1TableGen
import Std.Data.HashMap
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
   more than one projection in one `Signal` (`Signal d (A × B)` is ONE packed port, so
   it stays refused at `multi-output`).  A result that is a `×`-tree of
   `Signal d _` is multi-output (`stmtOf`): the statement is the lambda
   `fun xs => bundle2 (decl xs).1 (decl xs).2` (nested by the tree), whose
   table has one projection per leaf, and the port names are derived from the
   tree by the synthesizer's rule (`portNamesOf`: `out_0`, `out_1`, nested
   `out_0_1`, …, left-first; Sparkle/Compiler/Elab.lean `splitReturnLeaves`).
   They must be EXACTLY the returned module's output names (else
   `multi-output`); widths are checked by `ShapeStmt`, every port's value by
   `OutputsStmt`.  Register-free bodies only; structure results stay refused
   at `table`;
2. calls `synthesizeCombinational declName` exactly ONCE (the function
   `#synthesizeVerilog` calls; main has no inliner fuel guard) and keeps the
   returned `(m, design)`.  The guarantee is about that returned module, not
   the Verilog the command prints (`toVerilog (optimizeModule m)`);
3. registers `declName.ved_mod : Module := toExpr m` (and checks, by
   evaluating that closed term back and comparing with `m` by `DecidableEq`,
   that the term denotes the very value returned), the contract
   `declName.ved_contract := contractOf tbl <port names> clkRst declName.ved_mod`
   and the output list `declName.ved_outs`;
4. builds the expected type `U1Stmt declName.ved_contract declName.ved_mod
   stmt` as an `Expr`, where `stmt` (built by `stmtOf`) is the ORIGINAL
   constant `@declName`, or `@declName defaultDomain` when step 1 specialised
   it (then the theorem is about that specialisation, not about every domain
   of the polymorphic declaration; the OK line says "specialised at
   defaultDomain"), or, for a result that is a `×`-tree of signals, the
   bundled lambda `fun xs => bundle2 (D xs).1 (D xs).2` (nested by the tree)
   over that same `D` (`bundledStmt`: projections of the original
   declaration's value, nothing else).  `checkU1E` / `vedU1EntryOn` accept any
   `stmt`; the link to the declaration is a property of the path
   `stmtOf` → `vedU1EntryS`, not of the checker alone.  It elaborates a generated
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
  (e.g. an `addDecl` of a registered name failing).  A runtime limit
  (heartbeats, recursion depth) while elaborating the proof is refused at
  `proof`, and one in the synchronous kernel `addDecl` at `kernel`.
  NOT in that form: interrupt exceptions (never caught by the elaborator),
  and heartbeat / max-recursion exceptions raised by `readTable`,
  or `synthesizeCombinational` before `checkU1` starts (the plain
  `try … catch` there does not catch runtime exceptions; they propagate as
  their own errors).

The proof script is UNTRUSTED (the kernel checks it).  This slice's script
covers register-free modules built from not/and/or/xor/add/sub/mux/slice,
two-field concatenation, `==`, constants and `kLut!` mux chains (lemmas in
Tools/VedU1Lemmas.lean; a body with `==` is closed by a kernel `decide` over the
input domain only when the data inputs total at most 16 bits; above that, inputs of
at most 6 bits are enumerated value by value and wider inputs stay symbolic, closed
by `simp` + `omega`), and modules with
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

/-- A one-bit port read back from its stream value. -/
theorem toNat_bne (x : Nat) (h : x < 2) : x = (x != 0).toNat := by
  rcases Nat.lt_or_ge x 1 with h0 | h1
  · have : x = 0 := by omega
    subst this; rfl
  · have : x = 1 := by omega
    subst this; rfl

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

/-- Definitions the declaration's body mentions that `simp` must unfold to reach the
operators: those of its own module (private helpers, `abbrev` constants) and
`Sparkle.IP` sub-modules. -/
def helperConsts (decl : Name) : MetaM (Array Name) := do
  let env ← getEnv
  let modOf (n : Name) := env.getModuleIdxFor? n
  -- transitive: a helper's own helpers (`lqrController` uses `clampSymC`, `mulQSig`, ...)
  let mut out : Array Name := #[]
  let mut todo : Array Name := #[decl]
  let mut seen : NameSet := NameSet.empty.insert decl
  while !todo.isEmpty do
    let cur := todo.back!
    todo := todo.pop
    let some (.defnInfo di) := env.find? cur | continue
    for c in di.value.getUsedConstants do
      if seen.contains c then continue
      let some (.defnInfo _) := env.find? c | continue
      if modOf c == modOf decl || (`Sparkle.IP).isPrefixOf c then
        seen := seen.insert c
        out := out.push c
        todo := todo.push c
  return out

open Tools.VedU1TableGen in
deriving instance Lean.ToExpr for Form
open Tools.VedU1TableGen in
deriving instance Lean.ToExpr for TblData

open Tools.VedU1TableGen in
/-- The constant-table data read from a module whose body is a `kLut!` mux chain (any sharing of
equal constants): position `p` defines `Wt t p`, the statements are constants, aliases, `eq` against
the single input and `mux`es, and `TblData.ok` (the same Bool the kernel re-evaluates) accepts.
Only picks the script variant; the kernel re-checks everything. -/
def tblDataOf? (m : Sparkle.IR.AST.Module) (inp : String) : Option Tools.VedU1TableGen.TblData := do
  let b := m.body
  guard (b.length % 4 == 2 && b.length ≥ 6)
  let t := (b.length - 2) / 4
  let iw ← match m.inputs with | [⟨_, .bitVector n⟩] => some n | _ => none
  let w ← match m.outputs with | [⟨_, .bitVector n⟩] => some n | _ => none
  let mut pos : Std.HashMap String Nat := {}
  let mut i := 0
  for s in b do
    match s with
    | .assign l _ => guard (l == Wt t i); pos := pos.insert l i
    | _ => failure
    i := i + 1
  let mut fl : Array Form := #[]
  for s in b do
    let .assign _ e := s | failure
    let f ← match e with
      | .const v w' => if v < 0 then none else some (Form.const v.toNat w')
      | .ref n => (pos.get? n).map Form.alias
      | .op .eq [.ref a, .ref c] => if a == inp then (pos.get? c).map Form.eqIn else none
      | .op .mux [.ref c, .ref x, .ref y] => do
        let c' ← pos.get? c; let x' ← pos.get? x; let y' ← pos.get? y
        some (Form.mux c' x' y')
      | _ => none
    fl := fl.push f
  let Fl := fl.toList
  let bpL := (List.range t).map fun k => match Fl.getD (3 * k + 1) (.const 0 0) with | .eqIn j => j | _ => 0
  let rtL := (List.range t).map fun k => match Fl.getD (3 * t + (t - k)) (.const 0 0) with | .mux _ r _ => r | _ => 0
  let rl := match Fl.getD (3 * t + 1) (.const 0 0) with | .mux _ _ f => f | _ => 0
  let D0 : TblData := { Fl, t, bpL, rtL, rl, tbl := [], last := 0, iw, w, inp }
  let tbl := (List.range t).map fun k => ((kv D0.Fn (rtL.getD k 0 + 1) (rtL.getD k 0))).getD 0
  let last := (kv D0.Fn (rl + 1) rl).getD 0
  let D : TblData := { D0 with tbl, last }
  guard (D.ok = true)
  pure D

/-- The generated (untrusted) proof script for `U1Stmt C M F`.  `reg?` is
the single register of the delay shape (name, width), `none` for a
register-free module. -/
def scriptFor (nm : Names) (F : Name) (nDom : Nat) (reg? : Option (String × Nat))
    (inNames : List String := []) (eqs : Bool := false) (fStx? : Option Term := none) (helpers : Array Name := #[]) (inWidths : List Nat := [])
    (tbl? : Option Name := none) :
    TermElabM Syntax := do
  -- the declaration's own helper definitions (private `byte16`, `abbrev` constants,
  -- sub-modules), unfolded by `simp`; untrusted, the kernel checks the result.  The
  -- last entry erases `Nat.reduceAdd`, which would turn the `m + n` result width of a
  -- concatenation into a literal and defeat the append lemmas (and keeps the list non-empty).
  let hsA : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    helpers.mapM fun n => `(Lean.Parser.Tactic.simpLemma| $(mkCIdent n):term)
  let hlp : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
    Syntax.TSepArray.ofElems ((hsA.map fun x => (⟨x.raw⟩ : TSyntax _)).push
      ⟨(← `(Lean.Parser.Tactic.simpErase| -Nat.reduceAdd)).raw⟩)
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
  -- multi-output: the statement term is the bundled lambda itself
  if let some fs := fStx? then f := fs
  let B := mkCIdent nm.body
  match reg? with
  | none =>
    -- a constant table (`kLut!` mux chain): NOT unfolded by `simp`.  The kernel checks that the body
    -- is `tblBody` of the table; `step_tblBody` evaluates it once (induction over the table), and
    -- the declaration's chain is compared with `lutBV` of the same table by `rfl`
    if let some dn := tbl? then
      if inNames.length == 1 then
        let insI := mkIdent `ins
        let sI := mkIdent `s
        let Dc := mkCIdent dn
        return ← `(by
          have hD : ($Dc).ok = true := by decide +kernel
          have hbody : ($M).body = ($Dc).body := by decide +kernel
          have hB : $B = ($M).body := rfl
          have hin : ($M).inputs.map (·.name) = [($Dc).inp] := by decide +kernel
          have hout : ∀ p ∈ ($M).outputs, p.name = "out" := by decide +kernel
          have hord : OrderOk $M $B = true := by
            rw [hB, hbody]
            exact Tools.VedU1TableGen.orderOk_table $Dc hD $M hbody hin hout
          have hw : ($M).wires.map (·.name) = ($Dc).inp :: (List.range (4 * ($Dc).t + 1)).map (Tools.VedU1TableGen.Wt ($Dc).t) := by
            decide +kernel
          have hnd : (($M).wires.map (·.name)).Nodup := by
            rw [hw]; exact Tools.VedU1TableGen.nodup_table $Dc hD
          have hregs : ∀ r ∈ regsOf ($M).body, ∃ p ∈ ($M).wires, p.name = r.1 ∧ scalar p.ty = true := by
            intro r hr
            rw [hbody, Tools.VedU1TableGen.TblData.body, Tools.VedU1TableGen.regsOf_bodyN] at hr
            exact absurd hr (List.not_mem_nil)
          refine ⟨by decide +kernel, by decide +kernel, ⟨hnd, by decide +kernel, by decide +kernel, hregs⟩, ⟨$B, hord⟩, ?_⟩
          apply outputs_of_order $B hord
          apply outputs_of_step $C $M $B $f $O (by decide +kernel) (fun _ _ _ => True)
          · intro _ _; trivial
          · intro $insI hok $sI st mems _
            have hdi : ($C).dataInputs = [⟨($Dc).inp, .bitVector ($Dc).iw⟩] := by decide +kernel
            have hin1 : $insI $sI ($Dc).inp < 2 ^ declWidth $M ($Dc).inp :=
              hok.1 $sI ⟨($Dc).inp, .bitVector ($Dc).iw⟩ (by rw [hdi]; exact List.mem_singleton_self _)
            have hdw : declWidth $M ($Dc).inp = ($Dc).iw := by decide +kernel
            rw [hdw] at hin1
            rw [hB, hbody]
            obtain ⟨envF, hstep, hout'⟩ := Tools.VedU1TableGen.step_table $Dc hD (declWidth $M) mems
              (seedIn $M $insI $sI st)
            refine ⟨envF, [], mems, hstep, ?_, trivial⟩
            intro o ho
            simp only [$O:ident, List.mem_singleton] at ho
            subst ho
            rw [hout']
            have hseed : seedIn $M $insI $sI st ($Dc).inp = $insI $sI ($Dc).inp := by simp [seedIn, hin]
            rw [hseed]
            simp [srcOf, $C:ident, contractOf, applyIns, OTy.obs, PTy.obs, PTy.sig]
            have hsig : ($f ⟨fun t => BitVec.ofNat ($Dc).iw ($insI t ($Dc).inp)⟩).val $sI =
                Tools.VedU1Table.lutBV ($Dc).iw ($Dc).w (BitVec.ofNat ($Dc).iw ($insI $sI ($Dc).inp)) 0 ($Dc).tbl ($Dc).last := rfl
            have hlen : ($Dc).tbl.length = ($Dc).t := (Tools.VedU1TableGen.TblData.ok_sound $Dc hD).2.2.1
            have hti : ($Dc).t ≤ 2 ^ ($Dc).iw := (Tools.VedU1TableGen.TblData.ok_sound $Dc hD).2.2.2.1
            exact (Tools.VedU1Table.lutBV_toNat ($Dc).iw ($Dc).w ($insI $sI ($Dc).inp) hin1 _ 0 _
              (by rw [hlen]; omega)).symm.trans (congrArg BitVec.toNat hsig.symm))
    -- the input domain closes what the rewriting leaves (`==` against constants,
    -- a table's mux chain) when the data inputs total at most 16 bits (`wide` below
    -- is false): every data input generalised, the goal reverted to
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
    let domSmall ← `(tactic| all_goals
      $dom*
      decide +kernel)
    -- a domain too large to enumerate (`2^(Σ widths) > 2^16`): only the narrow
    -- inputs (the `==` selectors, ≤ 6 bits) are case-split, wide data stays symbolic
    -- and the leftover `BitVec` field extraction is closed by `omega`
    let wide := inWidths.length == inNames.length && inWidths.foldl (· + ·) 0 > 16
    let domAll : Array (TSyntax `tactic) ←
      if !wide then pure #[domSmall] else do
        let mut gen : Array (TSyntax `tactic) := #[]
        let k := inNames.length
        for i in [0:k] do
          let mut t : Term := hinI
          for _ in [0:i] do t ← `($t.2)
          if i + 1 < k then t ← `($t.1)
          gen := gen.push (← `(tactic| all_goals have $(hs[i]!):ident := $t))
        for (n, (x, h)) in inNames.zip (xs.zip hs) do
          gen := gen.push (← `(tactic| all_goals generalize $insI $sI $(Syntax.mkStrLit n) = $x at $h:ident ⊢))
        -- `x < 2^w` becomes `x = 0 ∨ … ∨ x = 2^w - 1`, then one goal per value
        let hc := mkIdent `hcase
        let rflI := mkIdent `rfl
        let mut narrow : Array (TSyntax `tactic) := #[]
        for (w, x, h) in inWidths.zip (xs.zip hs) do
          if w ≤ 6 then
            let mut dj : Term ← `($x = $(Syntax.mkNumLit (toString (2 ^ w - 1))))
            for v in (List.range (2 ^ w - 1)).reverse do
              dj ← `($x = $(Syntax.mkNumLit (toString v)) ∨ $dj)
            narrow := narrow.push (← `(tactic| all_goals (have $hc:ident : $dj := (by omega); clear $h:ident)))
            narrow := narrow.push (← `(tactic| all_goals (repeat' first | (rcases $hc:ident with $rflI:ident | $hc:ident) | subst $hc:ident)))
        -- the wide values are in range: `x % 2^w` folds back to `x`
        let mut modLs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
        for (w, h) in inWidths.zip hs do
          if w > 6 then
            modLs := modLs.push (← `(Lean.Parser.Tactic.simpLemma| Nat.mod_eq_of_lt $h:ident))
            modLs := modLs.push (← `(Lean.Parser.Tactic.simpLemma| $h:ident))
        let modL : Syntax.TSepArray [``Lean.Parser.Tactic.simpStar, ``Lean.Parser.Tactic.simpErase, ``Lean.Parser.Tactic.simpLemma] "," :=
          Syntax.TSepArray.ofElems (modLs.map fun x => (⟨x.raw⟩ : TSyntax _))
        pure (gen ++ narrow ++ (#[← `(tactic| all_goals ((try simp [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Tools.VedU1Lemmas.bit1_eq, Tools.VedU1Lemmas.toNat_append', BitVec.toNat_neg, BitVec.toInt_eq_toNat_cond, Sparkle.IR.Semantics.toSigned, Tools.VedU1Lemmas.or_hi_8, Tools.VedU1Lemmas.or_hi_16, Tools.VedU1Lemmas.or_hi_24, Tools.VedU1Lemmas.or_hi_32, Tools.VedU1Lemmas.or_hi_40, Tools.VedU1Lemmas.or_hi_48, Tools.VedU1Lemmas.or_hi_64, Tools.VedU1Lemmas.and_mod_r, Tools.VedU1Lemmas.and_mod_l, Tools.VedU1Lemmas.toNat_sshiftRight', Tools.VedU1Lemmas.toInt_ofNat_toSigned, Tools.VedU1Lemmas.beq_ofNat, Tools.VedU1Lemmas.toNat_decide_ite, Tools.VedU1Lemmas.toNat_not_decide_ite, Tools.VedU1Lemmas.toNat_ite_true, Tools.VedU1Lemmas.ofNat_eq_iff, Tools.VedU1Lemmas.ule_decide, Tools.VedU1Lemmas.ult_decide, Tools.VedU1Lemmas.xor_one_one, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, apply_ite BitVec.toNat, -Nat.reduceAdd, $modL,*]) <;> (first | omega | ((repeat' split) <;> (try simp only [Nat.reduceAdd, Nat.reducePow, Nat.reduceMod, Nat.reduceMul, Nat.reduceXor, Nat.reduceOr, Nat.reduceAnd, Nat.reduceDiv, Tools.VedU1Lemmas.xor_one_one, not_true_eq_false] at *) <;> omega))))] : Array (TSyntax `tactic)))
    -- a body with `==` goes straight to the input domain (the range tactics
    -- below only fail on it, after costly case splits)
    let tail : Array (TSyntax `tactic) ←
      if eqs then pure domAll else pure (#[
        -- one goal per output (several outputs)
        ← `(tactic| all_goals
          first
          | omega
          -- a `Bool` port
          | exact toNat_bne _ (by omega)
          -- a `mux`: both arms in range
          | (split <;> simp <;> omega)
          -- a `concat`: fields in range
          | (rw [BitVec.toNat_append]; simp [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt $hinI.1, Nat.mod_eq_of_lt $hinI.2])
          | skip)] ++ domAll)
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
            Tools.VedU1Lemmas.evalOp_eq_lit, Tools.VedU1Lemmas.evalOp_mul_lit, Tools.VedU1Lemmas.evalOp_shl_lit, Tools.VedU1Lemmas.evalOp_shr_lit, Tools.VedU1Lemmas.evalOp_lt_u_lit, Tools.VedU1Lemmas.evalOp_le_u_lit, Tools.VedU1Lemmas.evalOp_gt_u_lit, Tools.VedU1Lemmas.evalOp_ge_u_lit, Tools.VedU1Lemmas.evalOp_lt_s_lit, Tools.VedU1Lemmas.mul_val, Tools.VedU1Lemmas.add_val_sc, Tools.VedU1Lemmas.add_val_cs, Tools.VedU1Lemmas.sub_val_sc, Tools.VedU1Lemmas.sub_val_cs, Tools.VedU1Lemmas.mul_val_sc, Tools.VedU1Lemmas.mul_val_cs, Tools.VedU1Lemmas.and_val_sc, Tools.VedU1Lemmas.and_val_cs, Tools.VedU1Lemmas.or_val_sc, Tools.VedU1Lemmas.or_val_cs, Tools.VedU1Lemmas.xor_val_sc, Tools.VedU1Lemmas.xor_val_cs, Tools.VedU1Lemmas.shl_val_sc, Tools.VedU1Lemmas.shl_val_cs, Tools.VedU1Lemmas.shr_val_sc, Tools.VedU1Lemmas.shr_val_cs, Tools.VedU1Lemmas.append_def_sc, Tools.VedU1Lemmas.append_def_cs, Tools.VedU1Lemmas.evalOp_asr_lit, Tools.VedU1Lemmas.toNat_sshiftRight', Tools.VedU1Lemmas.mask_emod, Tools.VedU1Lemmas.slt_eq, Tools.VedU1Lemmas.ult_eq, Signal.slt, Signal.ult, Signal.ule, Signal.ashr, Signal.lt, Signal.le, Tools.VedU1Lemmas.bool_and_val, Tools.VedU1Lemmas.bool_or_val, Tools.VedU1Lemmas.bool_xor_val, Tools.VedU1Lemmas.bool_compl_val, Tools.VedU1Lemmas.evalOp_not_raw, Tools.VedU1Lemmas.evalOp_and_raw, Tools.VedU1Lemmas.evalOp_or_raw, Tools.VedU1Lemmas.evalOp_xor_raw, Tools.VedU1Lemmas.evalOp_sub_raw, Tools.VedU1Lemmas.shl_val, Tools.VedU1Lemmas.shr_val, BitVec.toNat_mul, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq', Tools.VedU1Lemmas.pure_val, Tools.VedU1Lemmas.append_def, Tools.VedU1Lemmas.toNat_append', Sparkle.Core.Signal.Signal.map,
            Seq.seq, Signal.beq, Signal.seq, Signal.ap, Sparkle.Core.Signal.bundle2, BitVec.toNat_append,
            BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt, Functor.map, Signal.map, BitVec.toNat_not, BitVec.toNat_ofNat,
            List.lookup, Option.getD_some, Option.getD_none, $hlp,*]
          -- several outputs: one goal per output
          try (repeat' apply And.intro)
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

/-- The synthesizer's output port names for the leaves of a result tree
(`splitReturnLeaves`, Sparkle/Compiler/Elab.lean): a leaf is named by its
prefix, `out` at the root; the two sides of a product get the suffixes `_0`
and `_1`.  Left-first, the order of `OTy.flat` and of `m.outputs`. -/
def portNamesOf : String → OTy → List String
  | pre, .leaf _ => [pre]
  | pre, .pair a b => portNamesOf (pre ++ "_0") a ++ portNamesOf (pre ++ "_1") b

open Lean Meta in
/-- Bundle a value of type `Signal d A × (Signal d B × …)` into one `Signal d
(A × …)` by `Signal.bundle2`, following the product tree of the TYPE `ty`
(a `Signal _ _` is a leaf).  The statement is then about the stream of
every projection, each observed at its own port. -/
partial def bundleProd (ty e : Lean.Expr) : MetaM Lean.Expr := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``Prod, #[a, b]) =>
    let l ← bundleProd a (← mkAppM ``Prod.fst #[e])
    let r ← bundleProd b (← mkAppM ``Prod.snd #[e])
    mkAppM ``Sparkle.Core.Signal.bundle2 #[l, r]
  | (``Sparkle.Core.Signal.Signal, _) => pure e
  | _ => throwError "{ty} is not a product of signals"

open Lean Meta in
/-- `fun xs => bundleProd (stmt xs)` for the statement `stmt` whose result
type is a product of signals (a `Prod` at the top). -/
def bundledStmt (stmt : Lean.Expr) : MetaM Lean.Expr := do
  forallTelescopeReducing (← inferType stmt) fun xs res => do
    unless (← whnfR res).isAppOf ``Prod do throwError "the result is not a product of signals"
    mkLambdaFVars xs (← bundleProd res (mkAppN stmt xs))

/-- Does an expression use `Operator.eq`? (only picks the script variant) -/
partial def exprHasEq : Sparkle.IR.AST.Expr → Bool
  | .op .eq _ => true
  | .op _ args | .concat args => args.any exprHasEq
  | .slice e _ _ | .sliceDim e _ _ => exprHasEq e
  | .index a i => exprHasEq a || exprHasEq i
  | _ => false

def bodyHasEq (body : List Sparkle.IR.AST.Stmt) : Bool :=
  body.any fun | .assign _ e => exprHasEq e | _ => false

/-- Resource budget for ELABORATING the generated script only (a finite bound,
not a check: the kernel still checks the result in full).  A table of `n`
entries is an `n`-deep `mux` chain; `simp` over it recurses once per level (the
default `maxRecDepth` 512 is exceeded from about 30 levels) and costs more than
the default heartbeats. -/
register_option ved.u1.proofRecDepth : Nat := {
  defValue := 20000
  descr := "VED U1: lower bound on maxRecDepth while elaborating the generated proof script (0 = the caller's limit only)" }
register_option ved.u1.proofHeartbeats : Nat := {
  defValue := 8000000
  descr := "VED U1: lower bound (thousands) on maxHeartbeats while elaborating the generated proof script (0 = the caller's limit only)" }

/-- The budget is read from the options in scope (defaults 20000 / 8000000):
the stage checks set both to 0 so that their own small context limits are the
ones that apply. -/
def withProofBudget {α} (k : TermElabM α) : TermElabM α :=
  withTheReader Core.Context
    (fun c => { c with
      maxRecDepth := max c.maxRecDepth (ved.u1.proofRecDepth.get c.options),
      maxHeartbeats := max c.maxHeartbeats (ved.u1.proofHeartbeats.get c.options * 1000) }) k

/-- The same finite recursion budget for the checker's own evaluation of `toExpr m` back to a
module (`Meta.evalExpr` compiles the closed term, which recurses once per list element:
a body of several hundred statements, a 256-entry table, exceeds the default
`maxRecDepth`, and that compiler reads the OPTION, not only the context).  A bound, not a
check: what the term denotes is still compared with `m` and the kernel checks the proof. -/
def withEvalBudget {α} (k : TermElabM α) : TermElabM α := do
  let d := ved.u1.proofRecDepth.get (← getOptions)
  withOptions (fun o => if d == 0 then o else o.set `maxRecDepth (max (maxRecDepth.get o) d))
    (withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth d }) k)

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
A runtime limit while elaborating the proof is refused at `proof`, one in the
synchronous kernel `addDecl` at `kernel` (not at `checker`).

`checkU1` verifies "this `m` has this declaration's meaning": the contract
reads the module name from `m` and does not bind it to `stmt`, so a
same-meaning `m` with another module name may be proved with a NEW proof.
That the entry inspects and returns the `m` it received, unsubstituted, is a
property of `vedU1Entry`, not of this statement. -/
def checkU1E (decl : Name) (base : Name) (stmt : Lean.Expr) (m : Sparkle.IR.AST.Module) (proof : ProofSrc)
    (outNames : List String := ["out"]) : TermElabM Name := do
  let nm := Names.ofBase base
  let saved ← saveState
  tryCatchRuntimeEx (do
    -- the table, from the TYPE of the statement's term
    let tbl ← try readTableOfType decl (← inferType stmt) catch e => refuse decl "table" e.toMessageData
    -- more than one projection only for a statement bundled from a product of
    -- signals (`bundledStmt`, a lambda); a constant with a `Signal (A × B)`
    -- result is ONE packed port, not two
    unless tbl.out.flat.length == 1 || !stmt.getAppFn.isConst do
      refuse decl "multi-output"
        m!"{tbl.out.flat.length} output projections in one `Signal` (the synthesizer packs it into one port `out`); refused"
    unless outNames.length == tbl.out.flat.length do
      refuse decl "multi-output"
        m!"{outNames.length} output port names for {tbl.out.flat.length} output projections"
    if !stmt.getAppFn.isConst && (regsOf m.body).length != 0 then
      refuse decl "multi-output" m!"multi-output with registers is not supported (register-free bodies only)"
    -- the closed term of `m`, checked to denote `m` itself
    let mE := toExpr m
    let back ← withEvalBudget (evalModule mE)
    unless decide (back = m) do
      refuse decl "artifact" m!"toExpr of the returned module does not evaluate back to it"
    let modTy := Lean.mkConst ``Sparkle.IR.AST.Module
    addDefn nm.mod modTy mE
    let some (.defnInfo di) := (← getEnv).find? nm.mod | refuse decl "artifact" m!"{nm.mod} missing"
    unless di.value == mE do refuse decl "artifact" m!"{nm.mod} does not hold toExpr m"
    let clkRst := clkRstOf m
    let cE := mkAppN (Lean.mkConst ``contractOf)
      #[toExpr tbl, toExpr outNames, toExpr clkRst, Lean.mkConst nm.mod]
    addDefn nm.contract (Lean.mkConst ``Contract) cE
    let c := contractOf tbl outNames clkRst m
    addDefn nm.outs (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Port))
      (toExpr c.outputs)
    -- the order-free meaning needs one well-ordered arrangement of the body
    let b0 := orderBody m.body
    unless OrderOk m b0 do
      refuse decl "order"
        m!"no arrangement of the body assigns every wire before it is read (combinational cycle, self-read, undriven net or duplicate update)"
    addDefn nm.body (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt))
      (toExpr b0)
    -- the full expected statement over `stmt` (the original constant, or the
    -- bundled lambda over it, from `stmtOf`)
    let expected := mkAppN (Lean.mkConst ``U1Stmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
    try check expected catch e => refuse decl "type" e.toMessageData
    unless ← isProp expected do refuse decl "type" m!"expected statement is not a Prop"
    -- elaborate the proof (errors are not turned into sorry)
    let inNames := (dataPortsOf m clkRst).map fun p => p.name
    let tblD? : Option Name ← do
      let inp := inNames.headD ""
      if let .generated := proof then
        if stmt.getAppFn.isConst && (regsOf m.body).isEmpty && inNames.length == 1 && decide (b0 = m.body) then
          if let some D := tblDataOf? m inp then
            let dn := nm.mod.getPrefix ++ `ved_tbl
            addDefn dn (Lean.mkConst ``Tools.VedU1TableGen.TblData) (toExpr D)
            pure (some dn)
          else pure none
        else pure none
      else pure none
    let stx ← match proof with
      | .generated =>
        let widths := m.inputs.filter (fun p => match clkRstOf m with | some (k, r) => p.name != k && p.name != r | none => true) |>.map fun p => match p.ty with | .bitVector w => w | .bit => 1 | _ => 100
        if stmt.getAppFn.isConst then
          scriptFor nm stmt.getAppFn.constName! stmt.getAppNumArgs (regShape m) inNames (bodyHasEq m.body) none (← helperConsts stmt.getAppFn.constName!) widths
            tblD?
        else scriptFor nm decl 0 none inNames (bodyHasEq m.body) (some (← Term.exprToSyntax stmt)) (← helperConsts decl) widths
      | .term s => pure s
      | .built mk => try mk nm m catch e => refuse decl "proof" e.toMessageData
    let errsBefore := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
    -- a runtime limit (heartbeats, recursion depth) here is a `proof` refusal
    -- (the script is too costly), not the catch-all `checker`
    -- (aff81fa7's size-scaled budget is replaced by `withProofBudget`: the limits are
    -- max(caller, `ved.u1.proofRecDepth` / `ved.u1.proofHeartbeats`), not a fixed
    -- multiple of the caller's; a caller with `maxHeartbeats 0` (unlimited) gets the
    -- finite option value)
    let pf ← tryCatchRuntimeEx
        (withProofBudget do
        withoutErrToSorry do
          let e ← elabTermEnsuringType stx expected
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e)
        fun e => refuse decl "proof" e.toMessageData
    let errs := (← Core.getMessageLog).toList.filter (·.severity == .error)
    if errs.length != errsBefore then
      let first ← match errs.drop errsBefore with
        | msg :: _ => msg.data.toString
        | [] => pure ""
      refuse decl "proof" m!"errors were logged while elaborating the proof; first: {first}"
    if pf.hasMVar || pf.hasFVar then refuse decl "proof" m!"proof term is not closed"
    -- the kernel, synchronously, with EXACTLY the expected type
    tryCatchRuntimeEx
      (withOptions (fun o => o.setBool `Elab.async false) do
        addDecl (.thmDecl { name := nm.thm, levelParams := [], type := expected, value := pf }))
      fun e => refuse decl "kernel" e.toMessageData
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

/-- The statement and the output port names for `declName`, from its TYPE:
the declaration itself (one output projection, port `out`), or, for a result
that is a product of `Signal`s, the bundled lambda (`bundledStmt`) with the
ports `portNamesOf`.  Refuses (stage `table` / `multi-output`) everything
else, before any synthesis. -/
def stmtOf (declName : Name) : TermElabM (Lean.Expr × Nat × List String) := do
  -- leading `DomainConfig` binders are instantiated with `defaultDomain`
  -- (the statement is then about `@declName defaultDomain`, NOT the
  -- polymorphic declaration); anything else is left for the table to refuse
  let (stmt, nDom) ← try specialiseDomain declName catch e => refuse declName "table" e.toMessageData
  let ty ← inferType stmt
  match ← (try pure (Except.ok (← readTableOfType declName ty)) catch e => pure (Except.error e)) with
  | .ok tbl =>
    unless tbl.out.flat.length == 1 do
      refuse declName "multi-output"
        m!"{tbl.out.flat.length} output projections in one `Signal` (the synthesizer packs it into one port `out`); refused"
    return (stmt, nDom, ["out"])
  | .error e =>
    -- a product of signals?
    let b ← try bundledStmt stmt catch _ => refuse declName "table" e.toMessageData
    let tbl ← try readTableOfType declName (← inferType b) catch e => refuse declName "table" e.toMessageData
    return (b, nDom, portNamesOf "out" tbl.out)

/-- The checker for a module `m` (the entry: the one `synthesizeCombinational`
returned): the statement from `declName`'s type, the output ports DERIVED
from the declaration's result tree by the synthesizer's rule and REQUIRED to
be exactly `m.outputs`' names (count, order), widths and the rest by
`ShapeStmt`. -/
def vedU1EntryOn (declName : Name) (stmt : Lean.Expr) (nDom : Nat) (names : List String)
    (m : Sparkle.IR.AST.Module) : TermElabM (Name × Nat) := do
  unless m.outputs.map (·.name) == names do
    refuse declName "multi-output"
      m!"the module's output ports {m.outputs.map (·.name)} are not the declaration's projections' ports {names}"
  let thm ← checkU1E declName declName stmt m .generated names
  return (thm, nDom)

/-- The U1 entry: `synthesizeCombinational` ONCE, the full statement over the
returned module and the declaration itself, kernel, strict audit; `m` is
returned only on success.  Failures of the steps before `checkU1` are tagged
(`table`, `multi-output`, `inliner`, `synthesis`) but NOT rolled back (see the
module docstring: runtime-limit exceptions there are not caught). -/
def vedU1EntryS (declName : Name) : TermElabM (Sparkle.IR.AST.Module × Design × Name × Nat) := do
  let (stmt, nDom, names) ← stmtOf declName
  let (m, d) ← try Sparkle.Compiler.Elab.synthesizeCombinational declName
    catch e => refuse declName "synthesis" e.toMessageData
  let (thm, _) ← vedU1EntryOn declName stmt nDom names m
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
