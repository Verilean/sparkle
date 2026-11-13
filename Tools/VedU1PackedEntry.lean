import Tools.VedU1Entry
import Tools.VedU1Packed
import Tools.VedU1MultiSeq

/-!
# U1 entry for a packed result `Signal d (A × B)` (`#ved_u1_packed decl`)

An explicit mode next to `#ved_u1` (which still refuses such a declaration at
`[multi-output]`; `Tools/VedU1Entry.lean` is not changed).  Same path:
specialise a leading `DomainConfig` binder, read the table from the declaration's TYPE, call
`synthesizeCombinational` ONCE, register `ved_mod`, `ved_contract` (here a `PContract`),
`ved_outs`, `ved_body`, elaborate the generated script against `PackedStmt c m stmt`, add the theorem with exactly
that type, strict audit.  Register-free bodies use `packedScript` (then `packedCombScript`); bodies with
registers (`Signal.loop`) use `packedLoopScript` (Tools/VedU1MultiSeq.lean), the contract then carrying the
module's clock/reset and register initial values (`PContract.clkRst` / `inits`, bound by `ShapeCore`).  The
result must be a `Prod` tree of at least two leaves inside ONE `Signal` (`Bool` / `BitVec w` leaves).

Refusals (`VED U1 REFUSED <decl> [<stage>]`; the `ved_*` constants the checker registered after it
started are taken back; side effects of synthesis before that, e.g. IO or caches, are NOT rolled back): `table`, `packed` (not a packed
result, the module's ports are not exactly `out`, or the slice map does not pass `PackCover`:
width / order / offset mismatch, overlap, missing slice), `synthesis`, `artifact`, `order`, `type`, `proof`, `kernel`, `audit`.
The slice map is DERIVED from the declaration's type by the packing rule (`OTy.slices`); the checker
below takes it as a parameter ONLY so that the controls can inject a wrong map.
-/

namespace Tools.VedU1PackedEntry

open Sparkle.IR.AST Sparkle.IR.Type Sparkle.IR.Semantics
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract Tools.VedU1Entry Tools.VedU1Packed
open Lean Meta Elab Term

deriving instance Lean.ToExpr for PContract

/-- The generated (untrusted) script for `PackedStmt C M f` (register-free). -/
def packedScript (nm : Names) (F : Name) (nDom : Nat) : TermElabM Syntax := do
  let C := mkCIdent nm.contract
  let M := mkCIdent nm.mod
  let O := mkCIdent nm.outs
  let B := mkCIdent nm.body
  let fI := mkCIdent F
  let mut f : Term := fI
  if nDom > 0 then
    f ← `(@$fI)
    for _ in [0:nDom] do f ← `($f Sparkle.Core.Domain.defaultDomain)
  `(by
      have hP : PackCover $C := by decide
      have hU : U1Stmt (PContract.core $C) $M (packedF ($C).tbl $f) := by
        refine ⟨by decide, by decide, by decide, ⟨$B, by decide⟩, ?_⟩
        apply outputs_of_order $B (by decide)
        apply outputs_of_step (PContract.core $C) $M $B (packedF ($C).tbl $f) $O (by decide) (fun _ _ _ => True)
        · intro _ _; trivial
        · intro ins hok s st mems _
          have key : srcOf (PContract.core $C) (packedF ($C).tbl $f) ins "out" s =
              OTy.packNat ($C).tbl.out ((applyIns ($C).tbl.ins ($C).inNames ins $f).val s) :=
            srcOf_packed $C $f ins s
          have hin := hok.1 s
          simp only [$O:ident, List.mem_singleton, forall_eq, key]
          simp [PContract.core, collapse, $C:ident, Contract.dataInputs, $M:ident, declWidth] at hin
          simp [stepModule, evalAssigns, regNexts, memNexts, Sparkle.IR.Semantics.evalExpr,
            Sparkle.IR.Semantics.evalList, Sparkle.IR.Semantics.evalExpr.go,
            widthOf, seedIn, applyNexts, $O:ident, $M:ident, $B:ident, declWidth,
            PContract.core, collapse, $C:ident, applyIns, $fI:ident,
            OTy.packNat, OTy.width, PTy.width, OTy.obs, PTy.obs, PTy.sig,
            mask,
            Nat.shiftRight_eq_div_pow, hin,
            Tools.VedU1Lemmas.evalOp_and_lit, Tools.VedU1Lemmas.evalOp_or_lit,
            Tools.VedU1Lemmas.evalOp_xor_lit, Tools.VedU1Lemmas.and_val,
            Tools.VedU1Lemmas.or_val, Tools.VedU1Lemmas.xor_val,
            Tools.VedU1Lemmas.evalOp_add_lit, Tools.VedU1Lemmas.add_val, BitVec.toNat_add,
            Tools.VedU1Lemmas.evalOp_sub_lit, Tools.VedU1Lemmas.sub_val, BitVec.toNat_sub,
            Tools.VedU1Lemmas.evalOp_mux_lit, Tools.VedU1Lemmas.mux_val,
            Tools.VedU1Lemmas.evalOp_not_lit, Tools.VedU1Lemmas.compl_val,
            Seq.seq, Signal.seq, Signal.ap, Sparkle.Core.Signal.bundle2, BitVec.toNat_append,
            BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt, Functor.map, Signal.map,
            BitVec.toNat_not, BitVec.toNat_ofNat, BitVec.toNat_ofBool,
            List.lookup, Option.getD_some, Option.getD_none]
          all_goals
            first
            | omega
            | (simp (disch := ltb) only [bne_toNat, Nat.mod_eq_of_lt] <;> (try simp (disch := ltb) only [cat_eq]) <;> omega)
            | (rw [Nat.mod_eq_of_lt (by omega)])
            | exact toNat_bne _ (by omega)
            | (split <;> simp <;> omega)
            | (rw [BitVec.toNat_append]; simp [BitVec.toNat_ofNat]; rw [Nat.mod_eq_of_lt hin.1, Nat.mod_eq_of_lt hin.2])
            | skip
      exact ⟨hP, hU, slices_of_outputs hP.1 hU.2.2.2.2⟩)

/-- The checker under the packed entry: like `checkU1E`, over a `PContract`.  `slices` is the
slice map put into the contract (the entry: `tbl.out.slices`); `m` the module. -/
def checkPackedE (decl : Name) (stmt : Lean.Expr) (tbl : DeclTable) (slices : List (Nat × Nat))
    (m : Sparkle.IR.AST.Module) (proof : ProofSrc) : TermElabM Name := do
  let nm := Names.ofBase decl
  let saved ← saveState
  tryCatchRuntimeEx (do
    unless tbl.out.flat.length ≥ 2 do
      refuse decl "packed" m!"the result is not a product inside one `Signal`"
    let pc : PContract :=
      { modName := m.name, tbl, port := "out", slices,
        inNames := tbl.binders.map ("_gen_" ++ ·), wires := m.wires,
        clkRst := clkRstOf m, inits := (regsOf m.body).map (fun r => (r.1, r.2.2.2)) }
    unless m.outputs.map (·.name) == ["out"] do
      refuse decl "packed" m!"the module's output ports {m.outputs.map (·.name)} are not the one packed port `out`"
    unless decide (PackCover pc) do
      refuse decl "packed"
        m!"the slice map {slices} is not the packing rule's map for the declaration's result, or does not cover the port exactly (width, order, offset, overlap, missing slice)"
    let mE := toExpr m
    let back ← withEvalBudget (evalModule mE)
    unless decide (back = m) do
      refuse decl "artifact" m!"toExpr of the returned module does not evaluate back to it"
    addDefn nm.mod (Lean.mkConst ``Sparkle.IR.AST.Module) mE
    let some (.defnInfo di) := (← getEnv).find? nm.mod | refuse decl "artifact" m!"{nm.mod} missing"
    unless di.value == mE do refuse decl "artifact" m!"{nm.mod} does not hold toExpr m"
    let pcE := toExpr pc
    addDefn nm.contract (Lean.mkConst ``PContract) pcE
    addDefn nm.outs (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Port))
      (toExpr pc.core.outputs)
    let b0 := orderBody m.body
    unless OrderOk m b0 do
      refuse decl "order" m!"no arrangement of the body assigns every wire before it is read"
    addDefn nm.body (mkApp (Lean.mkConst ``List [Level.zero]) (Lean.mkConst ``Sparkle.IR.AST.Stmt))
      (toExpr b0)
    let expected := mkAppN (Lean.mkConst ``PackedStmt) #[Lean.mkConst nm.contract, Lean.mkConst nm.mod, stmt]
    try check expected catch e => refuse decl "type" e.toMessageData
    unless ← isProp expected do refuse decl "type" m!"expected statement is not a Prop"
    -- a body with registers: the optional extra floor `ved.u1.seqProofHeartbeats` (default 0: none)
    let budget {α} (k : TermElabM α) : TermElabM α :=
      if (regsOf m.body).isEmpty then k else Tools.VedU1MultiSeq.withSeqBudget k
    -- elaborate a script against the expected statement (errors are not turned into sorry)
    let elabProof (stx : Syntax) : TermElabM Lean.Expr := do
      let errsBefore := (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
      let pf ← tryCatchRuntimeEx
          (budget <| withProofBudget do
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
      return pf
    let pf ← match proof with
      | .generated =>
        let F := stmt.getAppFn.constName!
        if (regsOf m.body).isEmpty then
          -- the register-free script first; a body it does not cover (comparisons against constants,
          -- wide operands) is retried with the loop script's unfolding and closing, without the loop
          let st ← saveState
          try elabProof (← packedScript nm F stmt.getAppNumArgs)
          catch e0 =>
            unless ← isRefusal e0 do throw e0
            st.restore (restoreInfo := true)
            try elabProof (← Tools.VedU1MultiSeq.packedCombScript nm F stmt.getAppNumArgs (← helperConsts F))
            catch _ => throw e0
        else
          elabProof (← Tools.VedU1MultiSeq.packedLoopScript nm F stmt.getAppNumArgs
            ((regsOf m.body).map fun r => (r.1, declWidth m r.1)) (← helperConsts F))
      | .term s => elabProof s
      | .built mk => elabProof (← try mk nm m catch e => refuse decl "proof" e.toMessageData)
    tryCatchRuntimeEx
      (budget <| withProofBudget <| withOptions (fun o => o.setBool `Elab.async false) do
        addDecl (.thmDecl { name := nm.thm, levelParams := [], type := expected, value := pf }))
      fun e => refuse decl "kernel" e.toMessageData
    let some (.thmInfo ti) := (← getEnv).find? nm.thm
      | refuse decl "kernel" m!"{nm.thm} is not a theorem in the environment"
    unless ti.type == expected do refuse decl "type" m!"stored type differs from the expected statement"
    try discard <| Tools.VedStrictAudit.strictAudit nm.thm
    catch e => refuse decl "audit" e.toMessageData
    return nm.thm) fun e => do
    saved.restore (restoreInfo := true)
    if ← isRefusal e then throw e
    refuse decl "checker" e.toMessageData

/-- The statement term and table of a packed declaration, from its TYPE (before any synthesis). -/
def packedStmtOf (declName : Name) : TermElabM (Lean.Expr × Nat × DeclTable) := do
  let (stmt, nDom) ← try specialiseDomain declName catch e => refuse declName "table" e.toMessageData
  let tbl ← try readTableOfType declName (← inferType stmt) catch e => refuse declName "table" e.toMessageData
  unless tbl.out.flat.length ≥ 2 do
    refuse declName "packed" m!"the result is not a product inside one `Signal` (use `#ved_u1`)"
  return (stmt, nDom, tbl)

/-- The packed entry: the module `synthesizeCombinational` returned, the statement over it and the
declaration, kernel, strict audit.  `m` is returned only on success. -/
def vedU1PackedS (declName : Name) : TermElabM (Sparkle.IR.AST.Module × Name × Nat) := do
  let (stmt, nDom, tbl) ← packedStmtOf declName
  let (m, _) ← try Sparkle.Compiler.Elab.synthesizeCombinational declName
    catch e => refuse declName "synthesis" e.toMessageData
  let thm ← checkPackedE declName stmt tbl tbl.out.slices m .generated
  return (m, thm, nDom)

/-- `#ved_u1_packed decl`. -/
elab "#ved_u1_packed " id:ident : command => do
  let decl ← Command.liftCoreM <| realizeGlobalConstNoOverload id
  Command.liftTermElabM do
    let (m, thm, nDom) ← vedU1PackedS decl
    let r ← Tools.VedStrictAudit.strictAudit thm
    let spec := if nDom > 0 then " (specialised at defaultDomain)" else ""
    logInfo m!"VED U1 PACKED OK {thm}{spec}: {Tools.VedStrictAudit.showNames r.axioms}\n{repr m}"

end Tools.VedU1PackedEntry
