/-
U1 measurement controls for the packed-port route `u1_packed` and its probe
(MEASUREMENT ONLY, never for main).

Run (after `kjob lake build Tools.VedU1PackedEntry Tools.VedStrictAudit Sparkle`):
  kjob lake env lean scripts/ved/controls/U1PackedControls.lean
The file elaborates without error iff every control holds; each prints
`VED U1CTL <id> PASS`.  The probe definition below (`#vedu1_packed_probe`) is the
text of PACKED_PROBE_DEF in scripts/ved/u1_gen.py, verbatim (a Python test checks
that); the controls run THAT probe, never a copy written for the control.

  P0  hand-made packed declarations: `#ved_u1_packed` registers the theorem and
      the probe ACCEPTS: THM theorem, TYPE exact (the rebuilt `PackedStmt`
      <ved_contract> <ved_mod> <stmt>), SLICES equal (the probe's own packing
      rule from the declaration's type), PORT match, CONTRACT bound-to-mod,
      MOD closed, axioms std3 (P0a two leaves, P0b three leaves and an implicit
      `DomainConfig` binder: STMT domains=1);
  P1  a WRONG slice map in the stored contract (a hand-made declaration over the
      accepted module; the other facts are right): the probe rejects SLICES for
      swapped slices, a wrong offset, a wrong width, a missing slice, and for
      another leaf order (P1a..P1d, P1e);
  P2  a WRONG statement (the theorem is about another declaration): TYPE differs;
  P3  a WRONG module (the 16-bit output of another declaration): PORT differs and
      CONTRACT other;
  P4  a refused declaration (single output `one`, a register `reg1`): no theorem
      and no ved_* constant is left behind by `#ved_u1_packed`, and the probe
      sees no theorem.
-/
import Tools.VedU1PackedEntry
import Tools.VedStrictAudit

open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Packed

open Lean Meta in
partial def vedu1pLeaves (ty : Expr) : MetaM (List Nat) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFnArgs with
  | (``Prod, #[a, b]) => return (← vedu1pLeaves a) ++ (← vedu1pLeaves b)
  | (``Bool, #[]) => return [1]
  | (``BitVec, #[w]) =>
    match ← evalNat (← whnf (← instantiateMVars w)) with
    | some n => return [n]
    | none => throwError "non-literal BitVec width {w}"
  | _ => throwError "unsupported leaf type {ty}"

open Lean Meta in
partial def vedu1pPairs (e : Expr) : MetaM (List (Nat × Nat)) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, h, t]) =>
    let h ← whnf h
    match h.getAppFnArgs with
    | (``Prod.mk, #[_, _, a, b]) =>
      let some a ← evalNat (← whnf a) | throwError "non-literal offset {a}"
      let some b ← evalNat (← whnf b) | throwError "non-literal width {b}"
      return (a, b) :: (← vedu1pPairs t)
    | _ => throwError "not a pair {h}"
  | _ => throwError "not a list {e}"

open Lean Meta in
partial def vedu1pPorts (e : Expr) : MetaM (List (String × Nat)) := do
  let e ← whnf e
  match e.getAppFnArgs with
  | (``List.nil, _) => return []
  | (``List.cons, #[_, h, t]) =>
    let h ← whnf h
    match h.getAppFnArgs with
    | (``Sparkle.IR.AST.Port.mk, #[nm, ty]) =>
      let .lit (.strVal s) ← whnf nm | throwError "non-literal port name {nm}"
      let ty ← whnf ty
      match ty.getAppFnArgs with
      | (``Sparkle.IR.Type.HWType.bitVector, #[w]) =>
        let some w ← evalNat (← whnf w) | throwError "non-literal port width {w}"
        return (s, w) :: (← vedu1pPorts t)
      | _ => return (s, 0) :: (← vedu1pPorts t)
    | _ => throwError "not a port {h}"
  | _ => throwError "not a list {e}"

open Lean Elab Command Meta in
elab "#vedu1_packed_probe " id:ident : command => do
  try
    let n ← liftCoreM <| realizeGlobalConstNoOverload id
    let env ← getEnv
    let thm := n ++ `ved_u1
    let md := n ++ `ved_mod
    let ct := n ++ `ved_contract
    match env.find? thm with
    | none => logInfo m!"VED U1P THM absent"
    | some (.thmInfo _) => logInfo m!"VED U1P THM theorem"
    | some _ => logInfo m!"VED U1P THM not-a-theorem"
    -- the statement term, rebuilt here: the original constant applied to
    -- `defaultDomain` once per LEADING implicit binder of type exactly `DomainConfig`
    let k ← liftTermElabM do
      let ci ← getConstInfo n
      forallTelescope ci.type fun xs _ => do
        let mut k := 0
        for x in xs do
          let ld ← x.fvarId!.getDecl
          if !ld.binderInfo.isExplicit && ld.type.isConstOf `Sparkle.Core.Domain.DomainConfig then k := k + 1
          else break
        pure k
    logInfo m!"VED U1P STMT domains={k}"
    let stmt := mkAppN (mkConst n) (List.replicate k (mkConst `Sparkle.Core.Domain.defaultDomain)).toArray
    if let some (.thmInfo ti) := env.find? thm then
      let expected := mkAppN (mkConst ``Tools.VedU1Packed.PackedStmt) #[mkConst ct, mkConst md, stmt]
      logInfo m!"VED U1P TYPE {if ti.type == expected then "exact" else "differs"}"
      logInfo m!"VED U1P MVARS type={ti.type.hasMVar} value={ti.value.hasMVar} fvars={ti.type.hasFVar || ti.value.hasFVar}"
      logInfo m!"VED U1P LEVELS {ti.levelParams.length}"
      let ax ← liftCoreM <| collectAxioms thm
      logInfo m!"VED U1P AXIOMS {Tools.VedStrictAudit.showNames (Tools.VedStrictAudit.sortNames ax)}"
    match env.find? md with
    | none => logInfo m!"VED U1P MOD absent"
    | some (.defnInfo di) =>
      let closed := !di.value.hasMVar && !di.value.hasFVar && !di.value.hasLooseBVars
      logInfo m!"VED U1P MOD closed={closed} type={di.type == mkConst ``Sparkle.IR.AST.Module}"
    | some _ => logInfo m!"VED U1P MOD not-a-def"
    -- the packing rule, from the declaration's TYPE (`Signal d (A x B)`)
    let ws ← liftTermElabM do
      forallTelescopeReducing (← inferType stmt) fun _ res => do
        let res ← whnfR (← instantiateMVars res)
        match res.getAppFnArgs with
        | (``Sparkle.Core.Signal.Signal, #[_, a]) => vedu1pLeaves a
        | _ => throwError "result {res} is not a Signal"
    let total := ws.foldl (· + ·) 0
    let offs := (List.range ws.length).map fun i => (ws.drop (i + 1)).foldl (· + ·) 0
    let expSl := offs.zip ws
    let showSl (l : List (Nat × Nat)) := "[" ++ ",".intercalate (l.map fun (o, w) => s!"({o},{w})") ++ "]"
    logInfo m!"VED U1P LEAVES {ws.length} widths={ws} total={total}"
    -- the stored contract (`PContract`): slice map, port name, module name, wires
    match env.find? ct with
    | none => logInfo m!"VED U1P CONTRACT absent"
    | some (.defnInfo _) =>
      let c := mkConst ct
      let sl ← liftTermElabM <| vedu1pPairs (mkApp (mkConst ``Tools.VedU1Packed.PContract.slices) c)
      logInfo m!"VED U1P SLICES expected={showSl expSl} stored={showSl sl} {if sl == expSl then "equal" else "differs"}"
      let (cport, cmod, wiresEq, mname) ← liftTermElabM do
        let cport ← whnf (mkApp (mkConst ``Tools.VedU1Packed.PContract.port) c)
        let cmod ← whnf (mkApp (mkConst ``Tools.VedU1Packed.PContract.modName) c)
        let mname ← whnf (mkApp (mkConst ``Sparkle.IR.AST.Module.name) (mkConst md))
        let weq ← isDefEq (mkApp (mkConst ``Tools.VedU1Packed.PContract.wires) c)
          (mkApp (mkConst ``Sparkle.IR.AST.Module.wires) (mkConst md))
        pure (cport, cmod, weq, mname)
      let bound := cport == mkStrLit "out" && cmod == mname && wiresEq
      logInfo m!"VED U1P CONTRACT {if bound then "bound-to-mod" else "other"}"
    | some _ => logInfo m!"VED U1P CONTRACT not-a-def"
    -- the module's output ports: exactly one, named `out`, of the packed width
    if env.contains md then
      let ps ← liftTermElabM <| vedu1pPorts (mkApp (mkConst ``Sparkle.IR.AST.Module.outputs) (mkConst md))
      logInfo m!"VED U1P PORT module={ps} expect=[(out, {total})] {if ps == [("out", total)] then "match" else "differs"}"
    -- the output count of the STATEMENT term's type
    let tbl ← liftTermElabM do
      Tools.VedU1Contract.readTableOfType n (← Lean.Meta.inferType stmt)
    logInfo m!"VED U1P OUTS {tbl.out.flat.length}"
  catch e => logInfo m!"VED U1P PROBE failed: {← e.toMessageData.toString}"

open Lean Elab Command in
/-- Elaborate `#vedu1_packed_probe n`, drop its messages and require every pattern
in `pats` to occur in the probe's output (a pattern starting with `!` must NOT occur). -/
elab "#vedu1_pexpect " id:str n:ident pats:str* : command => do
  let saved := (← get).messages
  modify fun s => { s with messages := MessageLog.empty }
  elabCommand (← `(command| #vedu1_packed_probe $n))
  let infos ← (← get).messages.toList.mapM fun m => m.data.toString
  modify fun s => { s with messages := saved }
  let all := "\n".intercalate infos
  let has (p : String) := (all.splitOn p).length > 1
  for p in pats do
    let p := p.getString
    if p.startsWith "!" then
      let q := (p.drop 1).toString
      if has q then throwError m!"VED U1CTL {id.getString} FAIL: unexpected `{q}` in\n{all}"
    else if !has p then throwError m!"VED U1CTL {id.getString} FAIL: missing `{p}` in\n{all}"
  logInfo m!"VED U1CTL {id.getString} PASS"

open Lean Elab Command in
elab "#vedu1_absent " id:str n:ident : command => do
  if (← getEnv).contains n.getId then throwError m!"VED U1CTL {id.getString} FAIL: {n.getId} exists"
  logInfo m!"VED U1CTL {id.getString} absent {n.getId}"

open Lean Elab Command in
/-- the tool refuses (an error `VED U1 REFUSED <decl> [<stage>]`), leaving nothing behind -/
elab "#vedu1_refused " id:str stage:str c:command : command => do
  let saved := (← get).messages
  modify fun s => { s with messages := MessageLog.empty }
  elabCommand c
  let errs ← (← get).messages.toList.filterMapM fun m => do
    if m.severity == .error then pure (some (← m.data.toString)) else pure none
  modify fun s => { s with messages := saved }
  if errs.any (fun e => (e.splitOn s!"[{stage.getString}]").length > 1 && e.startsWith "VED U1 REFUSED") then
    logInfo m!"VED U1CTL {id.getString} refused at [{stage.getString}]"
  else throwError m!"VED U1CTL {id.getString} FAIL: no [{stage.getString}] refusal; errors: {errs}"

namespace VedPk
def pk2 (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b
def pk3 {dom : DomainConfig} (a : Signal dom (BitVec 8)) (b : Signal dom Bool)
    (c : Signal dom (BitVec 4)) : Signal dom (BitVec 8 × (Bool × BitVec 4)) := bundle2 a (bundle2 b c)
def pw (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) := bundle2 a b
def one (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := ~~~a
def reg1 (a : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8 × BitVec 8) :=
  bundle2 (Signal.register 0#8 a) a
end VedPk

/-! P0: positives -/
set_option Elab.async false in
#ved_u1_packed VedPk.pk2
#vedu1_pexpect "P0a" VedPk.pk2 "THM theorem" "STMT domains=0" "TYPE exact" "SLICES expected=[(4,8),(0,4)] stored=[(4,8),(0,4)] equal"
  "PORT module=[(out, 12)] expect=[(out, 12)] match" "CONTRACT bound-to-mod" "MOD closed=true type=true" "OUTS 2" "LEVELS 0"
  "MVARS type=false value=false fvars=false" "!differs" "!sorryAx" "!ofReduceBool"
set_option Elab.async false in
#ved_u1_packed VedPk.pk3
#vedu1_pexpect "P0b" VedPk.pk3 "THM theorem" "STMT domains=1" "TYPE exact"
  "SLICES expected=[(5,8),(4,1),(0,4)] stored=[(5,8),(4,1),(0,4)] equal"
  "PORT module=[(out, 13)] expect=[(out, 13)] match" "CONTRACT bound-to-mod" "OUTS 3" "!differs" "!sorryAx"
set_option Elab.async false in
#ved_u1_packed VedPk.pw

/-! P1..P3: hand-made facts for a declaration over the accepted module -/

namespace VedPk
noncomputable def pkWa (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b
noncomputable def pkWa.ved_mod : Sparkle.IR.AST.Module := pk2.ved_mod
noncomputable def pkWa.ved_contract : PContract := { pk2.ved_contract with slices := [(0,8),(8,4)], modName := pk2.ved_mod.name }
#guard_msgs (drop warning) in
theorem pkWa.ved_u1 : PackedStmt pkWa.ved_contract pkWa.ved_mod pkWa := sorry
end VedPk
#vedu1_pexpect "P1a" VedPk.pkWa "THM theorem" "TYPE exact" "SLICES expected=[(4,8),(0,4)] stored=[(0,8),(8,4)] differs" "PORT module=[(out, 12)] expect=[(out, 12)] match" "!equal"

namespace VedPk
noncomputable def pkWb (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b
noncomputable def pkWb.ved_mod : Sparkle.IR.AST.Module := pk2.ved_mod
noncomputable def pkWb.ved_contract : PContract := { pk2.ved_contract with slices := [(5,8),(0,4)], modName := pk2.ved_mod.name }
#guard_msgs (drop warning) in
theorem pkWb.ved_u1 : PackedStmt pkWb.ved_contract pkWb.ved_mod pkWb := sorry
end VedPk
#vedu1_pexpect "P1b" VedPk.pkWb "THM theorem" "TYPE exact" "SLICES expected=[(4,8),(0,4)] stored=[(5,8),(0,4)] differs" "PORT module=[(out, 12)] expect=[(out, 12)] match" "!equal"

namespace VedPk
noncomputable def pkWc (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b
noncomputable def pkWc.ved_mod : Sparkle.IR.AST.Module := pk2.ved_mod
noncomputable def pkWc.ved_contract : PContract := { pk2.ved_contract with slices := [(4,7),(0,4)], modName := pk2.ved_mod.name }
#guard_msgs (drop warning) in
theorem pkWc.ved_u1 : PackedStmt pkWc.ved_contract pkWc.ved_mod pkWc := sorry
end VedPk
#vedu1_pexpect "P1c" VedPk.pkWc "THM theorem" "TYPE exact" "SLICES expected=[(4,8),(0,4)] stored=[(4,7),(0,4)] differs" "PORT module=[(out, 12)] expect=[(out, 12)] match" "!equal"

namespace VedPk
noncomputable def pkWd (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b
noncomputable def pkWd.ved_mod : Sparkle.IR.AST.Module := pk2.ved_mod
noncomputable def pkWd.ved_contract : PContract := { pk2.ved_contract with slices := [(4,8)], modName := pk2.ved_mod.name }
#guard_msgs (drop warning) in
theorem pkWd.ved_u1 : PackedStmt pkWd.ved_contract pkWd.ved_mod pkWd := sorry
end VedPk
#vedu1_pexpect "P1d" VedPk.pkWd "THM theorem" "TYPE exact" "SLICES expected=[(4,8),(0,4)] stored=[(4,8)] differs" "PORT module=[(out, 12)] expect=[(out, 12)] match" "!equal"

namespace VedPk
noncomputable def pkWe (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b
noncomputable def pkWe.ved_mod : Sparkle.IR.AST.Module := pk2.ved_mod
noncomputable def pkWe.ved_contract : PContract := { pk2.ved_contract with slices := [(0,4),(4,8)], modName := pk2.ved_mod.name }
#guard_msgs (drop warning) in
theorem pkWe.ved_u1 : PackedStmt pkWe.ved_contract pkWe.ved_mod pkWe := sorry
end VedPk
#vedu1_pexpect "P1e" VedPk.pkWe "THM theorem" "TYPE exact" "SLICES expected=[(4,8),(0,4)] stored=[(0,4),(4,8)] differs" "PORT module=[(out, 12)] expect=[(out, 12)] match" "!equal"

/-! P2: the theorem is about ANOTHER declaration (same table, other body) -/
namespace VedPk
def pkS (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b
noncomputable def pkS.ved_mod : Sparkle.IR.AST.Module := pk2.ved_mod
noncomputable def pkS.ved_contract : PContract := pk2.ved_contract
#guard_msgs (drop warning) in
theorem pkS.ved_u1 : PackedStmt pkS.ved_contract pkS.ved_mod pk2 := sorry
end VedPk
#vedu1_pexpect "P2" VedPk.pkS "THM theorem" "TYPE differs" "SLICES expected=[(4,8),(0,4)] stored=[(4,8),(0,4)] equal"

/-! P3: the module of ANOTHER declaration (16-bit output) under a 12-bit contract -/
namespace VedPk
def pkM (a : Signal defaultDomain (BitVec 8)) (b : Signal defaultDomain (BitVec 4)) :
    Signal defaultDomain (BitVec 8 × BitVec 4) := bundle2 (~~~a) b
noncomputable def pkM.ved_mod : Sparkle.IR.AST.Module := pw.ved_mod
noncomputable def pkM.ved_contract : PContract := pk2.ved_contract
#guard_msgs (drop warning) in
theorem pkM.ved_u1 : PackedStmt pkM.ved_contract pkM.ved_mod pkM := sorry
end VedPk
#vedu1_pexpect "P3" VedPk.pkM "TYPE exact" "PORT module=[(out, 16)] expect=[(out, 12)] differs" "CONTRACT other"

/-! P4: refused declarations leave nothing behind and the probe sees no theorem -/
set_option Elab.async false in
#vedu1_refused "P4a" "packed" #ved_u1_packed VedPk.one
#vedu1_absent "P4a" VedPk.one.ved_u1
#vedu1_absent "P4a" VedPk.one.ved_mod
#vedu1_pexpect "P4a" VedPk.one "THM absent" "MOD absent" "CONTRACT absent"
set_option Elab.async false in
#vedu1_refused "P4b" "packed" #ved_u1_packed VedPk.reg1
#vedu1_absent "P4b" VedPk.reg1.ved_u1
#vedu1_pexpect "P4b" VedPk.reg1 "THM absent"
