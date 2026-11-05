import Lean
import Tools.ShippingGen5PTCorpusTele
import Tests.SignalLoopTest
set_option autoImplicit false
-- D.D-4 Q-C 2nd step, RowTeleEvAt of PTcorpus (Issue sparkle-ledger-dd4-deprows). No sorry / axiom / native_decide. The net delta of the ledger is NOT decided here.

/-! # `PTcorpus`: which rows the telescope evidence closes

Before: `RowTeleEvAt` for 10 of the 51 term rows (`Tests/Gen5/PTCorpusSpecCheck.lean`). Here:
1. the 51 rows are classified by the theorem that closes `RowTeleEvAt` (nullary 6, closed telescope 4, new `ptc_tele_*` 24), the count AFTER;
2. the env facts of the new theorems (`EnvForms`, `¬ IsDefn env D`) are evaluated in the real environment with the SAME shape (`FE`, `instantiateLevelParamsS`), strict `Expr.equal` (binder names are part of the comparison for the inner arrows);
3. the 17 open rows, each with the first binder that the evidence cannot cover (printed from the real declared type);
4. the bundles over one environment: the types of `ptcorpus_oblRowTypedV_envAt` / `ptcorpus_rowTeleEvAt_envAt`, the fields of `PTCorpusEnvFacts` (102) / `PTCorpusTeleFacts` / `PTCorpusTeleOpen` (17);
5. the four named obligations, re-classified; negative controls; `#print axioms`. -/
open Lean Meta

namespace Tests.Gen5.PTCorpusTeleCheck
open Tools.ShippingGen5PTCorpus Tools.ShippingGen5PTCorpusTele Tools.ShippingGen5ConstValueES Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueESL

def lvStr (ns : List Nat) : String := "[" ++ ", ".intercalate (ns.map toString) ++ "]"
def tagOf (n : Name) : String := (n.toString).replace "." "_"

/-- Decidable evaluation of the env fact `EnvForms` (`Post [] 0 j T bs`): the instantiated declared type of `c` is the telescope `bs`; binder names are free except the arrows inside a form. -/
def postB : Nat → Expr → List Binder → Bool
  | _, _, [] => true
  | j, .forallE _ (.sort _) B _, .ty :: bs => postB (j + 1) B bs
  | j, .forallE _ A B _, .tm F :: bs => Expr.equal A (FE [] 0 j F) && postB (j + 1) B bs
  | _, _, _ => false

def envFormsB (env : Lean.Environment) (c : Name) (ls : List Level) (bs : List Binder) : Bool :=
  match env.find? c with
  | none => false
  | some ci => postB 0 (instantiateLevelParamsS ci.levelParams ls ci.type) bs

def isDefnB (env : Lean.Environment) (c : Name) : Bool :=
  match env.find? c with
  | some (.defnInfo _) => true
  | _ => false

def teleTable : List (Name × List Level × String × List Binder × List Name) := [
  (`Add.mk, [.zero], "Add_mk", bs_A2, []),
  (`AndOp.mk, [.zero], "AndOp_mk", bs_A2, []),
  (`Complement.mk, [.zero], "Complement_mk", bs_A1, []),
  (`Div.mk, [.zero], "Div_mk", bs_A2, []),
  (`Mod.mk, [.zero], "Mod_mk", bs_A2, []),
  (`Mul.mk, [.zero], "Mul_mk", bs_A2, []),
  (`OrOp.mk, [.zero], "OrOp_mk", bs_A2, []),
  (`ShiftLeft.mk, [.zero], "ShiftLeft_mk", bs_A2, []),
  (`ShiftRight.mk, [.zero], "ShiftRight_mk", bs_A2, []),
  (`Sub.mk, [.zero], "Sub_mk", bs_A2, []),
  (`XorOp.mk, [.zero], "XorOp_mk", bs_A2, []),
  (`Neg.mk, [.zero], "Neg_mk", bs_A1, []),
  (`BEq.mk, [.zero], "BEq_mk", bs_BEq, [`Bool]),
  (`NatCast.mk, [.zero], "NatCast_mk", bs_NatC, [`Nat]),
  (`NatPow.mk, [.zero], "NatPow_mk", bs_NatP, [`Nat]),
  (`Array.mk, [.zero], "Array_mk", bs_List, [`List]),
  (`Inhabited.mk, [.succ .zero], "Inhabited_mk", bs_V, []),
  (`Sparkle.Core.Wireable.mk, [], "Sparkle_Core_Wireable_mk", bs_Wire, [`Nat]),
  (`List.nil, [.zero], "List_nil", bs_Nil, []),
  (`List.cons, [.zero], "List_cons", bs_Cons, [`List]),
  (`OfNat.mk, [.zero], "OfNat_mk", bs_OfNat, [`Nat]),
  (`Pow.mk, [.zero, .zero], "Pow_mk", bs_Pow, []),
  (`Prod.mk, [.zero, .zero], "Prod_mk", bs_Prod, []),
  (`PProd.mk, [.succ .zero, .succ .zero], "PProd_mk", bs_Prod, [])
]

def natLv : Nat → Level
  | 0 => .zero
  | n + 1 => .succ (natLv n)

def tmKeys : List (Name × List Nat × List Bool) := tmsTable.map fun e => (e.1, e.2.1, e.2.2.1)

/-- The binders of a declared type, pretty-printed, from the real environment. -/
def binderTypes (env : Lean.Environment) (c : Name) (ls : List Level) : MetaM (List String) := do
  match env.find? c with
  | none => return ["MISSING"]
  | some ci =>
    let mut e := instantiateLevelParamsS ci.levelParams ls ci.type
    let mut acc : Array String := #[]
    repeat
      match e with
      | .forallE _ A B _ =>
        acc := acc.push (toString (← ppExpr A))
        e := B
      | _ => break
    return acc.toList

run_meta do
  let env ← getEnv
  let tm := tmKeys
  let axOk (t : Name) : MetaM Unit := do
    unless env.contains t do throwError "{t} missing"
    let ax ← Lean.collectAxioms t
    unless ax.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) do throwError "{t}: non-standard axioms {ax}"
  let closed4 : List Name := [``Nat.succ, ``Int.ofNat, ``Int.negSucc, `Sparkle.Core.Domain.DomainConfig.mk]
  -- 1. classification of the 51 term rows
  let mut nullary : Array String := #[]
  let mut closed : Array String := #[]
  let mut viaForms : Array String := #[]
  let mut factFail : Array String := #[]
  let mut openRows : Array (Name × List Nat × List Bool) := #[]
  for (n, ns, ks) in tm do
    let key := s!"{n} {lvStr ns}"
    if ks.isEmpty then nullary := nullary.push key
    else if closed4.contains n then closed := closed.push key
    else
      let tg := tagOf n
      let thm := Name.mkStr `Tools.ShippingGen5PTCorpusTele s!"ptc_tele_{tg}"
      if env.contains thm then
        axOk thm
        match teleTable.find? (fun (m, l, _, _, _) => m == n && l.length == ns.length) with
        | none => factFail := factFail.push s!"{key} (not in the Check table)"
        | some (_, ls, _, bs, needs) =>
          let ok1 := envFormsB env n ls bs
          let ok2 := needs.all fun d => !isDefnB env d
          let ok3 := bs.map Binder.kind == ks
          if ok1 && ok2 && ok3 then viaForms := viaForms.push key
          else factFail := factFail.push s!"{key} (EnvForms {ok1}, not-defn {ok2}, kinds {ok3})"
      else openRows := openRows.push (n, ns, ks)
  logInfo s!"RowTeleEvAt, term rows of PTcorpus: {tm.length}\nBEFORE (PTCorpusSpecCheck): {nullary.size + closed.size}/{tm.length} (nullary {nullary.size} + closed telescope {closed.size})\nAFTER: {nullary.size + closed.size + viaForms.size}/{tm.length}  (= {nullary.size + closed.size} + {viaForms.size} rows closed by `rowTeleEvAt_of_forms`, env facts evaluated in the real environment)\nnew rows: {viaForms.toList}\nenv facts that FAILED in the real environment: {factFail.toList}"
  unless viaForms.size == 24 do throwError "forms rows: {viaForms.size}"
  unless factFail.isEmpty do throwError "env facts failed"
  unless nullary.size == 6 && closed.size == 4 do throwError "before: {nullary.size} {closed.size}"
  -- named premise EnvClosedL on the relevant declarations (sample: every declared type of the 51 rows is closed)
  let mut notClosed : Array String := #[]
  for (n, _, _) in tm do
    match env.find? n with
    | some ci => unless ci.type.looseBVarRange == 0 do notClosed := notClosed.push (toString n)
    | none => notClosed := notClosed.push s!"{n} missing"
  logInfo s!"declared types of the 51 rows with a loose bound variable (premise `EnvClosedL`, sampled here): {notClosed.toList}"
  unless notClosed.isEmpty do throwError "closedness"
  for c in [`Nat, `Bool, `List] do
    if isDefnB env c then throwError "{c} is a definition"
  -- 2. the open rows and the first binder the evidence cannot cover
  let mut openRep : Array String := #[]
  for (n, ns, ks) in openRows do
    let bts ← binderTypes env n (ns.map natLv)
    let why :=
      if n == `LE.mk || n == `LT.mk then "binder 2 `α → α → Prop`: the codomain is `Sort 0`; `TDenV` has no rule for a sort (`pi`/`tcon`/`tunfold`/`tlet`)"
      else if n == `BitVec.ofFin then "binder 2 `Fin (2 ^ w)` mentions the TERM argument `w` through `HPow.hPow` (a projection function: its unfolding is an `Expr.proj`, which `CVEKVB` has no rule for): no `CVEKV` derivation of `2 ^ w`"
      else if n == `Sparkle.Core.Signal.Signal.mk then "binder 3 `Stream α`: no `tys` row for `Stream` in `PTcorpus`; `Stream` is a definition (`tunfold` needs the body of the definition as an env fact)"
      else if n == `Sparkle.Core.HasDomain.mk then "binder 2 `outParam DomainConfig`: `outParam` is a definition (`tunfold`, an env fact on its body)"
      else "binder 3 `outParam (Sort _)`: `TeleEv.ty` demands the binder to BE a `Sort` (`A = .sort u`); the `outParam` wrapper is not"
    openRep := openRep.push s!"{n} {lvStr ns} kinds={ks} binders={bts}\n    reason: {why}"
  logInfo s!"RowTeleEvAt OPEN: {openRows.size}\n{String.intercalate "\n" openRep.toList}"
  unless openRows.size == 17 do throwError "open rows {openRows.size}"
  -- the third binder of `H*.mk` is `outParam (Sort _)`, not a sort: checked on the real type
  let hb ← binderTypes env `HAdd.mk [.zero, .zero, .zero]
  unless hb.length == 4 && (hb[2]!.startsWith "outParam") do throwError "HAdd.mk binders {hb}"
  -- 3. the bundles over one environment
  let ty1 ← inferType (mkConst ``ptcorpus_oblRowTypedV_envAt)
  let ty2 ← inferType (mkConst ``ptcorpus_rowTeleEvAt_envAt)
  let f1 := (getStructureFields env ``PTCorpusEnvFacts).size
  let f2 := (getStructureFields env ``PTCorpusTeleFacts).size
  let f3 := (getStructureFields env ``PTCorpusTeleOpen).size
  logInfo s!"bundle over `envAt cref w`:\nptcorpus_oblRowTypedV_envAt : {toString (← ppExpr ty1)}\nptcorpus_rowTeleEvAt_envAt : {toString (← ppExpr ty2)}\nPTCorpusEnvFacts: {f1} named env facts (51 rows); PTCorpusTeleFacts: {f2}; PTCorpusTeleOpen: {f3} (the residue, named Props, not assumed)"
  unless f1 == 102 && f3 == 17 do throwError "bundle fields {f1} {f3}"
  -- every `¬ IsDefn env D` field of `PTCorpusEnvFacts` in the real environment
  let mut ndFail : Array String := #[]
  let mut nd := 0
  for fld in getStructureFields env ``PTCorpusEnvFacts do
    let some ci := env.find? (``PTCorpusEnvFacts ++ fld) | continue
    let t := ci.type
    -- `∀ env, ¬ IsDefn env D`: peel the binder, match `Not (IsDefn env (const D))`
    let body := match t with
      | .forallE _ _ b _ => b
      | b => b
    match body with
    | .forallE _ (.app (.app (.const ``Tools.ShippingGen5ConstValueE.IsDefn _) _) (.const d _)) _ _ =>
      nd := nd + 1
      if isDefnB env d then ndFail := ndFail.push s!"{fld}: {d}"
    | .app (.const ``Not _) (.app (.app (.const ``Tools.ShippingGen5ConstValueE.IsDefn _) _) (.const d _)) =>
      nd := nd + 1
      if isDefnB env d then ndFail := ndFail.push s!"{fld}: {d}"
    | _ => pure ()
  logInfo s!"`¬ IsDefn env D` fields of PTCorpusEnvFacts evaluated in the real environment: {nd}, failing {ndFail.toList}. The other fields (`EnvTypeL` / `EnvClosedPiL` / `EnvDepFirst` / `EnvDepSpine`) are evaluated by PTCorpusCheck / PTCorpusSpecCheck."
  unless ndFail.isEmpty do throwError "defn"
  -- 4. the four named obligations
  for t in [``oblTeleEv_Fin_mk_PTcorpus, ``oblTeleEv_Decidable_isTrue_PTcorpus, ``oblTeleEv_Decidable_isFalse_PTcorpus,
            ``rowTypedV_Fin_mk_PTcorpus, ``rowTypedV_Decidable_isTrue_PTcorpus, ``rowTypedV_Decidable_isFalse_PTcorpus, ``control_bitVec_ofFin_has_row] do axOk t
  for c in [``Fin.mk, ``Decidable.isTrue, ``Decidable.isFalse] do
    if tm.any (fun (m, _, _) => m == c) then throwError "{c} has a row"
  unless tm.any (fun (m, _, _) => m == ``BitVec.ofFin) do throwError "BitVec.ofFin has no row"
  logInfo s!"The four named obligations (Prop proof terms / binders outside Type 0):\n* Fin.mk (isLt : val < n): the binder is a PROOF (a term of a Prop); a `Dyn` has `ty : Type`, so no argument can carry it. `MissingWhy.propBinder`: NO row in `PTcorpus`. `OblTeleEv_Fin_mk PTcorpus env` and `RowTypedAtV` hold with no hypothesis (`oblTeleEv_Fin_mk_PTcorpus`, `rowTypedV_Fin_mk_PTcorpus`), by the absence of the row; no derivation reaches the key (count it under \"no row\", not as a typed row).\n* Decidable.isTrue / isFalse ((p : Prop) (h : p)): the type binder `p : Prop` is a `Sort 0` binder (outside `Type 0`, `TeleEv.ty` gives `Type` arguments) and `h` is a proof. NO row; both obligations hold vacuously (`oblTeleEv_Decidable_isTrue_PTcorpus` / `..isFalse..`, `rowTypedV_Decidable_*`).\n* BitVec.ofFin: HAS a row (`control_bitVec_ofFin_has_row`); `RowTypedAtV` is closed (spine); `RowTeleEvAt` is NOT: the binder `Fin (2 ^ w)` is a Type 0 binder that depends on a term argument, and its denotation needs a `CVEKV` derivation of `2 ^ w` (open row above)."
  -- 5. controls
  let lz : List Level := [.zero]
  unless envFormsB env `Add.mk lz bs_A2 do throwError "CONTROL: right shape rejected"
  if envFormsB env `Add.mk lz bs_A1 then throwError "CONTROL: wrong shape (T → T) accepted"
  if envFormsB env `Add.mk lz bs_NatC then throwError "CONTROL: wrong shape (Nat → T) accepted"
  if envFormsB env `Add.mk lz bs_BEq then throwError "CONTROL: wrong codomain accepted"
  if envFormsB env `Nonexistent.mk lz bs_A2 then throwError "CONTROL: missing constant accepted"
  if envFormsB env `HAdd.mk [.zero, .zero, .zero] [.ty, .ty, .ty, .tm fA2] then throwError "CONTROL: outParam binder accepted as a sort"
  if envFormsB env `Pow.mk [.zero, .zero] bs_Prod then throwError "CONTROL: Pow.mk with the shape of Prod.mk accepted"
  unless envFormsB env `Pow.mk [.zero, .zero] bs_Pow do throwError "CONTROL: Pow.mk right shape rejected"
  unless isDefnB env `Sparkle.Core.Domain.ResetKind do throwError "CONTROL: Domain.ResetKind should be a definition"
  axOk ``teleEv_forms
  axOk ``rowTeleEvAt_of_forms
  axOk ``post_subst
  axOk ``FE_subst
  axOk ``tdenF
  axOk ``ptcorpus_oblRowTypedV
  axOk ``ptcorpus_rowTeleEvAt
  axOk ``ptcorpus_oblRowTypedV_envAt
  axOk ``ptcorpus_rowTeleEvAt_envAt
  axOk ``closedL_envAt
  logInfo s!"CONTROLS ok: wrong shape / codomain / missing constant / `outParam` binder / swapped telescope rejected by the env-fact evaluator, right shapes accepted, a definition key (ResetKind) detected"

/-- NEGATIVE CONTROL (proved): a form that refers to a TERM binder is rejected by the well-formedness check (the evidence only exists for type binders). -/
example : wfB [.tm fNat, .tm v0] [] = false := by decide
example : wfB bs_A2 [] = true := by decide
/-- NEGATIVE CONTROL (proved): a form that refers to a binder that does not exist yet. -/
example : wfB [.tm (.var 3)] [] = false := by decide

end Tests.Gen5.PTCorpusTeleCheck

#print axioms Tools.ShippingGen5PTCorpusTele.post_subst
#print axioms Tools.ShippingGen5PTCorpusTele.teleEv_forms
#print axioms Tools.ShippingGen5PTCorpusTele.rowTeleEvAt_of_forms
#print axioms Tools.ShippingGen5PTCorpusTele.ptc_tele_Add_mk
#print axioms Tools.ShippingGen5PTCorpusTele.ptc_tele_Prod_mk
#print axioms Tools.ShippingGen5PTCorpusTele.ptcorpus_oblRowTypedV
#print axioms Tools.ShippingGen5PTCorpusTele.ptcorpus_rowTeleEvAt
#print axioms Tools.ShippingGen5PTCorpusTele.ptcorpus_oblRowTypedV_envAt
#print axioms Tools.ShippingGen5PTCorpusTele.ptcorpus_rowTeleEvAt_envAt
#print axioms Tools.ShippingGen5PTCorpusTele.oblTeleEv_Fin_mk_PTcorpus
