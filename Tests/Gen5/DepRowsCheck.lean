import Lean
import Sparkle
import Tests.Compiler.ShippingMachineEntryTest
import Tests.Compiler.NoPortsMemKidTest
import Tests.Compiler.ShippingChildBoundaryTest
import Tests.Compiler.ShippingMachineNestTest
import Tests.Compiler.ShippingMachineSeqTest
import Tests.Compiler.ShippingMachineTeleTest
import Tests.Compiler.KaryGenTest
import Tests.Compiler.KaryThreeTest
import Tests.Compiler.SharedLeafGenDefaultHbTest
import Tests.Compiler.SharedLeafGenFallbackTest
import Tests.Compiler.SharedLeafGenTest
import Tests.Compiler.SharedLeafMemKidTest
import Tests.Compiler.MultiInstanceTest
import IP.Bus.LINHW
import IP.Crypto.Keccak256HW
import IP.Crypto.Keccak256Sponge
import IP.Crypto.P256FieldHW
import IP.Crypto.P256OrderHW
import IP.Crypto.Secp256k1OrderHW
import IP.Net.HFTStrategy
import IP.Net.HTTP
import IP.Net.UART
import Tools.ShippingGen5DepRows
set_option autoImplicit false
/-! D.D-4 DepRows (issue sparkle-ledger-dd4-deprows): check of `Tools/ShippingGen5DepRows.lean`.
(1) model table (non-vacuity of the dom-fields specs, the generic theorem instantiates); (2) negative controls (proved); (3) the ENV FACTS of the 26 output-structure keys, checked in the real environment (meta mirrors of `EnvDepFirst` / `EnvDomFields`);
(4) the substitution obligation is not reached; (5) axioms, counts, remaining obligations. No TRUSTED / axiom / sorry / native_decide; `PT` stays arbitrary in the theorems (the model table is only here). -/
namespace Tests.Gen5.DepRowsCheck
open Lean Tools.ShippingGen5ConstValueE Tools.ShippingGen5ConstValueEKey Tools.ShippingGen5ConstValueESoundK Tools.ShippingGen5ConstValueES
  Tools.ShippingGen5ConstValueESL Tools.ShippingGen5ConstValueEVL Tools.ShippingGen5RowTypedV Tools.ShippingGen5DepRows

/-! ## (1) Model table: the specs of the dom-fields telescope are satisfiable and the generic theorem instantiates

`Tst.Out.mk (dom : DomainConfig) (f : Tst.Sig dom Nat) : Tst.Out dom`, with `Tst.Sig dom A := A` (a toy signal). -/
open Sparkle.Core.Domain in
open Classical in
noncomputable def outMkRow : TmRow :=
  ⟨[true, true], fun as => match as with
    | [.tm d0, .tm d1] => if d0.ty = DomainConfig ∧ d1.ty = Nat then some ⟨Unit, ()⟩ else none
    | _ => none⟩
def tyRowM (T : Type) : TyRow := ⟨[], fun _ => some T⟩
def sigRowM : TyRow := ⟨[true, false], fun as => match as with | [.tm _, .ty A] => some A | _ => none⟩
open Sparkle.Core.Domain in
noncomputable def PTq : PrimTableK :=
  ⟨fun D Ls =>
     if D == ``Nat && Ls.isEmpty then some (tyRowM Nat)
     else if D == `Sparkle.Core.Domain.DomainConfig && Ls.isEmpty then some (tyRowM DomainConfig)
     else if D == `Tst.Sig && Ls.isEmpty then some sigRowM
     else none,
   fun c ls => if c == `Tst.Out.mk && ls.isEmpty then some outMkRow else none⟩

open Sparkle.Core.Domain in
theorem sigSpecQ : SigRowSpec PTq `Tst.Sig [] DomainConfig (fun _ A => A) :=
  ⟨sigRowM, by simp [PTq], rfl, fun _ _ => rfl⟩

open Sparkle.Core.Domain in
theorem domFieldsSpecQ : DomFieldsSpec PTq `Tst.Out.mk [] DomainConfig (fun _ A => A) [Nat] := by
  refine ⟨outMkRow, by simp [PTq], rfl, ?_⟩
  intro as d h
  match as with
  | [.tm d0, .tm d1] =>
    simp only [outMkRow] at h
    split at h
    · rename_i hh
      obtain ⟨t0, v0⟩ := d0
      obtain ⟨hd0, hd1⟩ := hh
      simp only at hd0 hd1
      subst hd0
      refine ⟨v0, [.tm d1], rfl, ?_⟩
      exact And.intro hd1 trivial
    · cases h
  | [] => simp [outMkRow] at h
  | [.ty _] => simp [outMkRow] at h
  | [.tm _] => simp [outMkRow] at h
  | [.ty _, _] => simp [outMkRow] at h
  | [.tm _, .ty _] => simp [outMkRow] at h
  | _ :: _ :: _ :: _ => simp [outMkRow] at h

open Sparkle.Core.Domain in
example (env : Environment) (hnd : ¬ IsDefn env `Tst.Sig) (hnd2 : ¬ IsDefn env `Sparkle.Core.Domain.DomainConfig) (hnat : ¬ IsDefn env ``Nat)
    (hT : EnvDomFields env `Tst.Out.mk [] `Sparkle.Core.Domain.DomainConfig `Tst.Sig [] [.const ``Nat []]) : RowTeleEvAt PTq env `Tst.Out.mk [] :=
  rowTeleEvAt_domFields PTq env _ _ _ _ _ [.const ``Nat []] [Nat] DomainConfig (fun _ A => A) domFieldsSpecQ sigSpecQ hnd
    (fun _ => tdenv_const_nullary (row := tyRowM DomainConfig) (by simp [PTq]) hnd2 rfl rfl)
    ⟨fun _ => tdenv_const_nullary (row := tyRowM Nat) (by simp [PTq]) hnat rfl rfl, trivial⟩ hT

/-! ## (2) Negative controls (proved) -/
open Sparkle.Core.Domain in
/-- A row that accepts a `Nat` field does not satisfy the spec that says the field type is `Empty`. -/
theorem domFieldsSpec_wrong : ¬ DomFieldsSpec PTq `Tst.Out.mk [] DomainConfig (fun _ A => A) [Empty] := by
  rintro ⟨row, hrow, _, hden⟩
  have h1 : PTq.tms `Tst.Out.mk [] = some outMkRow := by simp [PTq]
  rw [h1] at hrow
  cases Option.some.inj hrow
  let dv : DomainConfig := ⟨0, .rising, .synchronous⟩
  have hd : outMkRow.den [.tm ⟨DomainConfig, dv⟩, .tm ⟨Nat, (0 : Nat)⟩] = some ⟨Unit, ()⟩ := by
    simp [outMkRow]
  obtain ⟨dv', rest, has, hs⟩ := hden _ _ hd
  injection has with _ htl
  subst htl
  obtain ⟨hty, _⟩ := hs
  have h : Nat = Empty := hty
  exact (Eq.mp h (0 : Nat)).elim

theorem argsAreSig_length {DCT : Type} (SigT : DCT → Type → Type) (dv : DCT) : ¬ ArgsAreSig SigT dv [Nat] [] := fun h => h

theorem alphaDen_length (PT : PrimTableK) (env : Environment) : ¬ AlphaDen PT env [.const ``Nat []] [] := fun h => h

/-- A field whose payload type is open (`bvar 0`) is not of the shape. -/
theorem fieldsPiB_open_payload (S : Name) (ℓs : List Level) (B : Expr) (x : Name) (bi : BinderInfo) :
    ¬ FieldsPiB S ℓs (.forallE x (Sig S ℓs (.bvar 0) (.bvar 0)) B bi) 0 [.bvar 0] := by
  rintro ⟨x', B', bi', h, hα, _⟩
  simp [lbr] at hα

/-- A field typed at the SECOND enclosing binder instead of the domain (`bvar 1` at the first field) is not of the shape. -/
theorem fieldsPiB_wrong_index (S : Name) (ℓs : List Level) (B : Expr) (x : Name) (bi : BinderInfo) (α : Expr) :
    ¬ FieldsPiB S ℓs (.forallE x (Sig S ℓs (.bvar 1) α) B bi) 0 [α] := by
  rintro ⟨x', B', bi', h, _⟩
  simp [Sig] at h

/-- The domain binder must be the constant `dc`: a `Nat` binder is not `DomPi` for `DomainConfig`. -/
theorem domPi_wrong_dom (S : Name) (ℓs : List Level) (B : Expr) :
    ¬ DomPi `Sparkle.Core.Domain.DomainConfig S ℓs (.forallE `d (.const ``Nat []) B .default) [] := by
  rintro ⟨x, B', bi, h, _⟩
  simp at h

/-! ## (3) ENV FACTS of the 26 keys in the real environment -/
def keys26 : List Name :=
  [`Sparkle.IP.Bus.LINHW.ChkOut,
   `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut,
   `Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut,
   `Sparkle.IP.Crypto.P256FieldHW.MulOut,
   `Sparkle.IP.Crypto.P256OrderHW.MulOut,
   `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut,
   `Sparkle.IP.Net.HFTStrategy.HFTOut,
   `Sparkle.IP.Net.HTTP.HttpEmitOut,
   `Sparkle.IP.Net.HTTP.HttpRequestParserOut,
   `Sparkle.IP.Net.UART.TxOut,
   `Sparkle.Tests.Compiler.MultiInstance.PeOut,
   `Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut,
   `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut,
   `Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut,
   `Sparkle.Tests.Compiler.ShippingMachineNestTest.Out,
   `Sparkle.Tests.Compiler.ShippingMachineNestTest.Pair,
   `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut,
   `Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut,
   `Sparkle.Tests.Compiler.ShippingMachineTeleTest.PulseOut,
   `Tests.Compiler.KaryGenTest.KOut,
   `Tests.Compiler.KaryThreeTest.KOut,
   `Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out,
   `Tests.Compiler.SharedLeafGenDefaultHbTest.AccOutD,
   `Tests.Compiler.SharedLeafGenFallbackTest.AccOutF,
   `Tests.Compiler.SharedLeafGenTest.Acc16Out,
   `Tests.Compiler.SharedLeafMemKidTest.MOut]

def piNB : Expr → Nat → Expr → Bool
  | T, 0, R => T == R
  | .forallE _ _ B _, n + 1, R => piNB B n R
  | _, _, _ => false
def nBinders : Expr → Nat
  | .forallE _ _ B _ => nBinders B + 1
  | _ => 0
def notDefn (env : Environment) (D : Name) : Bool :=
  match env.find? D with
  | some (.defnInfo _) => false
  | some _ => true
  | none => false
/-- shape `n + 1` binders, result `D Ls (bvar n)` (what `EnvDepFirst` says) -/
def depFirstB (T : Expr) (D : Name) (Ls : List Level) : Bool :=
  nBinders T ≥ 1 && piNB T (nBinders T) (.app (.const D Ls) (.bvar (nBinders T - 1)))

/-- mirror of `FieldsPiB`: returns the payload types (all with `lbr = 0`), the signal former (name, levels) and the remaining result -/
def fieldsB (T : Expr) (k : Nat) : Option (List Expr × Option (Name × List Level) × Expr) :=
  match T with
  | .forallE _ (.app (.app (.const s ls) (.bvar j)) α) B _ =>
    if j == k && lbr α == 0 then
      match fieldsB B (k + 1) with
      | some (as, none, R) => some (α :: as, some (s, ls), R)
      | some (as, some sl, R) => if sl == (s, ls) then some (α :: as, some sl, R) else none
      | none => none
    else none
  | R => some ([], none, R)

def DC : Name := `Sparkle.Core.Domain.DomainConfig

open Lean Meta in
run_meta do
  let env ← getEnv
  let mut ok : Nat := 0
  let mut dump : Array MessageData := #[]
  let mut formers : Array (Name × List Level) := #[]
  let mut payloads : Array String := #[]
  let mut nfields : Nat := 0
  for n in keys26 do
    let c := n ++ `mk
    let some ci := env.find? c | throwError "{c} absent"
    unless ci.levelParams.isEmpty do throwError "{c} has level parameters {ci.levelParams}"
    let T := ci.type
    let some D := (match env.find? n with | some (.inductInfo _) => some n | _ => none) | throwError "{n} is not an inductive"
    match T with
    | .forallE _ (.const d []) B _ =>
      unless d == DC do throwError "{c}: first binder is {d}"
      match fieldsB B 0 with
      | none => throwError "FieldsPiB fails for {c}: {T}"
      | some (αs, sl, R) =>
        -- result: `D (bvar (fields))`, and the `DomPi` / `EnvDepFirst` facts hold for it
        unless R == .app (.const D []) (.bvar αs.length) do throwError "result of {c} is not D (bvar n): {R}"
        unless depFirstB T D [] do throwError "EnvDepFirst fails for {c}"
        unless notDefn env D do throwError "{D} is a defnInfo"
        let ps := αs.foldl (fun (acc : Array String) α => let t := toString α; if acc.contains t then acc else acc.push t) #[]
        formers := if sl.isSome && !formers.contains sl.get! then formers.push sl.get! else formers
        payloads := ps.foldl (fun (acc : Array String) t => if acc.contains t then acc else acc.push t) payloads
        nfields := nfields + αs.length
        dump := dump.push m!"{c}: {αs.length} fields, {ps.size} distinct payload types"
        ok := ok + 1
    | _ => throwError "{c}: not a DomainConfig-first telescope"
  logInfo m!"per key:\n{MessageData.joinSep dump.toList "\n"}"
  logInfo m!"signal type formers used by the 26 keys: {formers}; {nfields} field binders in all; distinct payload types ({payloads.size}): {payloads}"
  unless formers.size == 1 do throwError "the 26 keys do not share one signal former"
  logInfo m!"env facts ok for {ok} output-structure keys (FieldsPiB with closed payloads, result D (bvar n), D not a definition)"

/-! ## (4) The row proofs do not reach the substitution obligation -/
open Lean Meta in
def reachable (env : Environment) (roots : List Name) (pfx : List Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo := roots
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match todo with
    | [] => break
    | n :: rest =>
      todo := rest
      if seen.contains n then continue
      seen := seen.insert n
      let some ci := env.find? n | continue
      if !(pfx.any (fun p => p.isPrefixOf n)) then continue
      let mut cs := ci.type.getUsedConstants
      if let some v := ci.value? then cs := cs ++ v.getUsedConstants
      for c in cs do
        if !seen.contains c then todo := c :: todo
  return seen

run_meta do
  let env ← getEnv
  let pfx : List Name := [`Tools.ShippingGen5DepRows, `Tools.ShippingGen5RowTypedV, `Tools.ShippingGen5ConstValueEVL, `Tools.ShippingGen5ConstValueEV, `Tools.ShippingGen5ConstValueESL, `Tools.ShippingGen5ConstValueES]
  let banned : List Name := [``OblDenSubstS, ``Tools.ShippingGen5ConstValueES.oblDenSubstS_safe, ``tdens_subst, ``argsdens_subst, ``cveks_subst, ``SubV, ``SafeArg]
  let roots : List Name := [``rowTypedAtV_depFirst, ``rowTeleEvAt_domFields, ``teleEv_fields, ``fieldsPiB_subst, ``fieldsPi_subst,
    ``rowTypedDep_LINHW_ChkOut]
  let seen := reachable env roots pfx
  let hit := banned.filter seen.contains
  unless hit.isEmpty do throwError "DepRows theorems reach banned substitution declarations: {hit}"
  let seenS := reachable env [``denTypedS] pfx
  unless seenS.contains ``OblDenSubstS do throwError "detector control FAILED: denTypedS must reach OblDenSubstS"
  logInfo m!"substitution check ok: the DepRows theorems reach {seen.size} declarations, none of {banned}"

/-! ## (5) Remaining named obligations, axioms, counts -/
run_meta do
  let env ← getEnv
  let remaining : List Name := [``OblTeleEv_Fin_mk, ``OblTeleEv_BitVec_ofFin, ``OblTeleEv_Decidable_isTrue, ``OblTeleEv_Decidable_isFalse,
    ``EnvDomFields, ``DomFieldsSpec, ``SigRowSpec, ``AlphaDen, ``FirstArgSpec, ``EnvDepFirst]
  let mut lines : Array MessageData := #[]
  for n in remaining do
    let some ci := env.find? n | throwError "{n} absent"
    if ci.isTheorem || (match ci with | .axiomInfo _ => true | _ => false) then throwError "{n} is a theorem/axiom, expected a Prop definition"
    lines := lines.push m!"  {n}"
  logInfo m!"named obligations / specs ({lines.size}; Prop definitions, none assumed):\n{MessageData.joinSep lines.toList "\n"}"

def stdAx : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def provedNames : List Name :=
  [``fieldsPiB_subst, ``fieldsPi_subst, ``teleEv_fields, ``rowTeleEvAt_domFields, ``rowTypedDep_Fin_mk, ``rowTypedDep_BitVec_ofFin,
   ``rowTypedDep_Decidable_isTrue, ``rowTypedDep_Decidable_isFalse, ``sigSpecQ, ``domFieldsSpecQ, ``domFieldsSpec_wrong, ``argsAreSig_length, ``alphaDen_length,
   ``fieldsPiB_open_payload, ``fieldsPiB_wrong_index, ``domPi_wrong_dom]

open Lean Meta in
run_meta do
  let env ← getEnv
  -- the 26 per-key RowTypedAtV / RowTeleEvAt theorems, found by name
  let mut rowT : Array Name := #[]
  let mut teleT : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if ci.isTheorem then
      match n with
      | .str (.str (.str .anonymous "Tools") "ShippingGen5DepRows") s =>
        if s.startsWith "rowTypedDep_" && !s.startsWith "rowTypedDep_Fin" && !s.startsWith "rowTypedDep_BitVec" && !s.startsWith "rowTypedDep_Decidable" then rowT := rowT.push n
        if s.startsWith "teleEvDep_" then teleT := teleT.push n
      | _ => pure ()
  unless rowT.size == 26 do throwError "expected 26 rowTypedDep_ theorems, found {rowT.size}"
  unless teleT.size == 26 do throwError "expected 26 teleEvDep_ theorems, found {teleT.size}"
  -- each per-key theorem is about its own key: the statement mentions the key's constructor name
  for n in keys26 do
    let c := n ++ `mk
    let key := "`" ++ c.toString
    let mentions (t : Name) : MetaM Bool := do
      let some ci := env.find? t | return false
      let str := toString (← ppExpr ci.type)
      return (str.splitOn key).length > 1
    let mut h1 : Nat := 0
    for t in rowT do if ← mentions t then h1 := h1 + 1
    unless h1 == 1 do throwError "key {c}: {h1} rowTypedDep theorems mention it"
    let mut h2 : Nat := 0
    for t in teleT do if ← mentions t then h2 := h2 + 1
    unless h2 == 1 do throwError "key {c}: {h2} teleEvDep theorems mention it"
  let all := provedNames ++ rowT.toList ++ teleT.toList
  let mut bad : Array Name := #[]
  for n in all do
    unless env.contains n do throwError "{n} absent"
    let ax ← Lean.collectAxioms n
    if ax.any (fun a => !stdAx.contains a) then bad := bad.push n
  unless bad.isEmpty do throwError "non-standard axiom (or sorryAx) in: {bad}"
  logInfo m!"axiom check ok: {all.length} proved declarations use only propext / Classical.choice / Quot.sound"
  logInfo m!"per-key theorems: RowTypedAtV {rowT.size} (output structures, one theorem each, each mentioning exactly its own key) + 4 named keys (Fin.mk, BitVec.ofFin, Decidable.isTrue/isFalse) = {rowT.size + 4}; RowTeleEvAt {teleT.size} (dom-fields evidence, one theorem each)"

axiom negControlAxiom : False
theorem negControlUsesAxiom : (1 : Nat) = 2 := negControlAxiom.elim
run_meta do
  let ax ← Lean.collectAxioms ``negControlUsesAxiom
  unless ax.contains ``negControlAxiom do throwError "negative control FAILED: detector missed the axiom"
  logInfo m!"negative control ok: detector flags {ax.toList}"

/-! ### Counts

Dependent keys of the corpus: 30 = 26 output structures `Foo.mk {dom : DomainConfig} fields : Foo dom` + `Fin.mk` + `BitVec.ofFin` + `Decidable.isTrue` + `Decidable.isFalse`.
`RowTypedAtV`: 30 per-key theorems (26 + 4 named), each a theorem with the row spec (`FirstArgSpec`, about `PT`) and the env fact (`EnvDepFirst`) as hypotheses; the env fact is confirmed in the real environment for the 26.
`RowTeleEvAt`: 26 per-key theorems from the dom-fields evidence shape (spec of the row, spec of the `Signal` row, payload denotations, env fact `EnvDomFields`, confirmed in the real environment for the 26); 4 remain named obligations (`OblTeleEv_*`) with reasons (propositions as arguments, `HPow` terms in a binder type, `Prop`-valued type arguments). -/
run_meta do
  let rowsProved : Nat := 26 + 4
  let teleProved : Nat := 26
  let teleRemaining : Nat := 4
  unless rowsProved + 0 == 30 && teleProved + teleRemaining == 30 do throwError "partition of the 30 dependent keys fails"
  logInfo m!"DepRows: RowTypedAtV per-key theorems {rowsProved} / 30 (remaining 0; PT spec FirstArgSpec and env fact EnvDepFirst are hypotheses); RowTeleEvAt per-key theorems {teleProved} / 30, remaining {teleRemaining}: Fin.mk, BitVec.ofFin, Decidable.isTrue, Decidable.isFalse (named obligations OblTeleEv_*, reasons in the file); ledger FG 75 / T1 57 unchanged"

end Tests.Gen5.DepRowsCheck

#print axioms Tools.ShippingGen5DepRows.rowTeleEvAt_domFields
#print axioms Tools.ShippingGen5DepRows.teleEv_fields
#print axioms Tools.ShippingGen5DepRows.fieldsPiB_subst
#print axioms Tools.ShippingGen5DepRows.fieldsPi_subst
#print axioms Tools.ShippingGen5DepRows.rowTypedDep_LINHW_ChkOut
#print axioms Tools.ShippingGen5DepRows.teleEvDep_LINHW_ChkOut
