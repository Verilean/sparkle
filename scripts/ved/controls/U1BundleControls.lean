/-
U1 measurement controls for the BUNDLED-statement check of the standard probe
(MEASUREMENT ONLY, never for main).  TEMPLATE: the two markers below are filled from
scripts/ved/u1_gen.py (BUNDLE_DEF and PROBE) so the probe tested here is the probe the harness
runs; scripts/ved/controls/gen_u1bundle_controls.py writes the .lean file, and the Python tests
check that the probe region has not drifted.

Run (after `kjob lake build Tools.VedU1Entry Tools.VedU1StructOut Tools.VedStrictAudit Sparkle`):
  python3 -I scripts/ved/controls/gen_u1bundle_controls.py OUT.lean
  kjob lake env lean OUT.lean
The file elaborates without error iff every control holds; each prints `VED U1BCTL <id> PASS`.

A declaration whose result is a structure / a product of signals is registered by `#ved_u1` with the
statement `U1Stmt c m (fun xs => bundle2 (D xs).f1 (bundle2 (D xs).f2 ...))`.  The probe rebuilds that
lambda itself (vedu1bTree: structure -> its projection functions in field order, `Prod` -> `.1`/`.2`,
`bundle2`, right-nested) and compares with `==`.

  B0  accepted declarations (entry + probe): a structure of two signals, a product of two signals, a
      structure of three fields, a nested product, a structure with an implicit `DomainConfig` binder:
      TYPE exact-bundled, BUNDLE leaves=n, OUTS n, std3 axioms, MOD closed, CONTRACT bound-to-mod;
  B1  a constant (single-`Signal`) declaration: unchanged, TYPE exact and no BUNDLE line;
  B2  a stored theorem over a bundle with two fields SWAPPED (`bundle2 (D a b).d (D a b).s`): TYPE differs;
  B3  a stored theorem over the bundle of a DIFFERENT declaration (same shape): TYPE differs;
  B4  product vs structure mix-up (the structure declaration's theorem carries the `.1`/`.2` bundle of a
      product declaration, and the product declaration's theorem carries the structure projections'
      bundle): TYPE differs both ways;
B2-B4 are hand-made theorems (`sorryAx`) over clones of the accepted declarations' contract and module:
only the TYPE line of the probe is asserted there.  (A bundle nested another way does not even
typecheck against the contract's table type, so it cannot be stored as a `U1Stmt` theorem.)
-/
import Tools.VedU1Entry
import Tools.VedU1StructOut
import Tools.VedStrictAudit

open Lean Elab Command Meta
open Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.VedU1Contract

namespace VedBCtl

structure S2 (dom : DomainConfig) where
  s : Signal dom (BitVec 8)
  d : Signal dom (BitVec 8)

structure S3 (dom : DomainConfig) where
  x : Signal dom (BitVec 8)
  y : Signal dom (BitVec 8)
  z : Signal dom Bool

def bs (a b : Signal defaultDomain (BitVec 8)) : S2 defaultDomain := { s := a + b, d := a - b }
def bsOther (a b : Signal defaultDomain (BitVec 8)) : S2 defaultDomain := { s := a ^^^ b, d := a - b }
def bsSw (a b : Signal defaultDomain (BitVec 8)) : S2 defaultDomain := { s := a + b, d := a - b }
def bsMix (a b : Signal defaultDomain (BitVec 8)) : S2 defaultDomain := { s := a + b, d := a - b }
def bp (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) × Signal defaultDomain (BitVec 8) :=
  (a + b, a - b)
def bpMix (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) × Signal defaultDomain (BitVec 8) :=
  (a + b, a - b)
def bs3 (a b : Signal defaultDomain (BitVec 8)) : S3 defaultDomain := { x := a + b, y := a - b, z := a === b }
def bpn (a b : Signal defaultDomain (BitVec 8)) :
    Signal defaultDomain (BitVec 8) × (Signal defaultDomain (BitVec 8) × Signal defaultDomain Bool) :=
  (a + b, (a - b, a === b))
def bsDom {dom : DomainConfig} (a b : Signal dom (BitVec 8)) : S2 dom := { s := a + b, d := a - b }
def one (a b : Signal defaultDomain (BitVec 8)) : Signal defaultDomain (BitVec 8) := a + b
end VedBCtl

-- the probe's bundle builder and the probe, verbatim from u1_gen.py
open Lean Meta in
partial def vedu1bTree (ty e : Expr) : MetaM (Expr × Nat) := do
  let ty ← whnfR (← instantiateMVars ty)
  match ty.getAppFn with
  | .const ``Sparkle.Core.Signal.Signal _ => return (e, 1)
  | .const ``Prod _ =>
    let #[a, b] := ty.getAppArgs | throwError "malformed product {ty}"
    let (l, ln) ← vedu1bTree a (← mkAppM ``Prod.fst #[e])
    let (r, rn) ← vedu1bTree b (← mkAppM ``Prod.snd #[e])
    return (← mkAppM ``Sparkle.Core.Signal.bundle2 #[l, r], ln + rn)
  | .const ind _ =>
    let some si := getStructureInfo? (← getEnv) ind | throwError "{ty} is not a structure"
    if si.fieldNames.isEmpty then throwError "{ind} has no fields"
    let mut leaves : Array (Expr × Nat) := #[]
    for f in si.fieldNames do
      let pj ← mkAppM (ind ++ f) #[e]
      leaves := leaves.push (← vedu1bTree (← inferType pj) pj)
    let mut acc := leaves.back!
    for i in (List.range (leaves.size - 1)).reverse do
      let (l, ln) := leaves[i]!
      acc := (← mkAppM ``Sparkle.Core.Signal.bundle2 #[l, acc.1], ln + acc.2)
    return acc
  | _ => throwError "{ty} is not a signal, a product or a structure"

open Lean Elab Command Meta in
elab "#vedu1b_probe " id:ident : command => do
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
    -- the statement term, rebuilt here independently of the entry: the
    -- original constant, applied to `defaultDomain` once per LEADING implicit
    -- binder whose type is exactly `DomainConfig` (reviewer 2026-11-10)
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
    -- a result that is a structure / `Prod` of signals: the expected statement is the bundled
    -- lambda built here (BUNDLE_DEF); any other result keeps the constant statement.  If the
    -- walk fails the declaration is checked as a constant, as before.
    let bundled? : Option (Expr × Nat) ← liftTermElabM do
      try
        forallTelescopeReducing (← inferType stmt) fun xs res => do
          let res ← whnfR (← instantiateMVars res)
          if res.getAppFn.isConstOf ``Sparkle.Core.Signal.Signal then return none
          let (bt, nl) ← vedu1bTree res (mkAppN stmt xs)
          return some (← mkLambdaFVars xs bt, nl)
      catch _ => return none
    let stmtT := match bundled? with | some (b, _) => b | none => stmt
    if let some (_, nl) := bundled? then logInfo m!"VED U1P BUNDLE leaves={nl}"
    if let some (.thmInfo ti) := env.find? thm then
      let expected := mkAppN (mkConst ``Tools.VedU1Contract.U1Stmt) #[mkConst ct, mkConst md, stmtT]
      logInfo m!"VED U1P TYPE {if ti.type == expected then (if bundled?.isSome then "exact-bundled" else "exact") else "differs"}"
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
    match env.find? ct with
    | none => logInfo m!"VED U1P CONTRACT absent"
    | some (.defnInfo di) =>
      let ok := di.value.getAppFn.isConstOf ``Tools.VedU1Contract.contractOf &&
        di.value.getAppArgs.back? == some (mkConst md)
      logInfo m!"VED U1P CONTRACT {if ok then "bound-to-mod" else "other"}"
    | some _ => logInfo m!"VED U1P CONTRACT not-a-def"
    -- the outputs of the STATEMENT term's type (`@decl defaultDomain` when
    -- specialised; readTable on the bare constant refuses its implicit binder)
    let tbl ← liftTermElabM do
      Tools.VedU1Contract.readTableOfType n (← Lean.Meta.inferType stmtT)
    logInfo m!"VED U1P OUTS {tbl.out.flat.length}"
  catch e => logInfo m!"VED U1P PROBE failed: {← e.toMessageData.toString}"

/-! ## Control plumbing -/

/-- Run `c`, capture its messages and drop them; every `has` must be a substring of some message,
no `lacks` may be, and no message may be an error. -/
elab "#vedu1b_expect " id:str "[" hs:str,* "]" "[" ls:str,* "]" c:command : command => do
  let saved := (← get).messages
  modify fun s => { s with messages := MessageLog.empty }
  elabCommand c
  let msgs ← (← get).messages.toList.mapM fun m => do pure (m.severity, ← m.data.toString)
  modify fun s => { s with messages := saved }
  let has (p : String) := msgs.any fun (_, t) => (t.splitOn p).length > 1
  let errs := msgs.filter (·.1 == .error)
  unless errs.isEmpty do throwError m!"VED U1BCTL {id.getString} FAIL: errors {errs.map (·.2)}"
  for h in hs.getElems do
    unless has h.getString do
      throwError m!"VED U1BCTL {id.getString} FAIL: expected line `{h.getString}` not found in {msgs.map (·.2)}"
  for l in ls.getElems do
    if has l.getString then
      throwError m!"VED U1BCTL {id.getString} FAIL: unexpected `{l.getString}` in {msgs.map (·.2)}"
  logInfo m!"VED U1BCTL {id.getString} PASS"

/-- The harness's two steps on one declaration: the tool, then the probe. -/
elab "#vedu1b_both " id:ident : command => do
  elabCommand (← `(set_option Elab.async false in #ved_u1 $id))
  elabCommand (← `(#vedu1b_probe $id))

/-- Clone the module and contract of `src` under `dst` (the contract bound to the clone's module) and
store a theorem `dst.ved_u1 : U1Stmt dst.ved_contract dst.ved_mod <stmt>` (`sorryAx`).  `stmt` is built
by `stmtOf`, which receives the variables of `dst`'s type telescope. -/
def cloneWith (src dst : Name) (stmtOf : Array Lean.Expr → MetaM Lean.Expr) :
    CommandElabM Unit := liftTermElabM do
  let env ← getEnv
  let some (.defnInfo dm) := env.find? (src ++ `ved_mod) | throwError "no {src}.ved_mod"
  let some (.defnInfo dc) := env.find? (src ++ `ved_contract) | throwError "no {src}.ved_contract"
  let mkD (n : Name) (ty v : Lean.Expr) : MetaM Unit :=
    addDecl (.defnDecl (mkDefinitionValEx n [] ty v .abbrev .safe []))
  mkD (dst ++ `ved_mod) dm.type dm.value
  mkD (dst ++ `ved_contract) dc.type
    (mkAppN dc.value.getAppFn (dc.value.getAppArgs.pop.push (mkConst (dst ++ `ved_mod))))
  let ci ← getConstInfo dst
  let stmt ← forallTelescopeReducing ci.type fun xs _ => do mkLambdaFVars xs (← stmtOf xs)
  let expected := mkAppN (mkConst ``U1Stmt) #[mkConst (dst ++ `ved_contract), mkConst (dst ++ `ved_mod), stmt]
  addDecl (.thmDecl { name := dst ++ `ved_u1, levelParams := [], type := expected,
                      value := mkApp2 (mkConst ``sorryAx [Level.zero]) expected (mkConst ``Bool.false) })

/-- projection `proj` (a constant) applied to `D xs` -/
def projOf (proj : Name) (e : Lean.Expr) : MetaM Lean.Expr := mkAppM proj #[e]

open Sparkle.Core.Signal in
/-- the bundle `bundle2 (f e) (g e)` -/
def bundleOf (f g : Lean.Expr → MetaM Lean.Expr) (e : Lean.Expr) : MetaM Lean.Expr := do
  mkAppM ``Sparkle.Core.Signal.bundle2 #[← f e, ← g e]

/-- `D xs` for the declaration `n` applied to the telescope -/
def app (n : Name) (xs : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) xs

/-! ## B0: accepted bundled declarations -/
#vedu1b_expect "B0-structure" [
    "VED U1 OK VedBCtl.bs.ved_u1",
    "VED U1P THM theorem", "VED U1P BUNDLE leaves=2", "VED U1P TYPE exact-bundled",
    "VED U1P MVARS type=false value=false fvars=false", "VED U1P LEVELS 0",
    "VED U1P MOD closed=true type=true", "VED U1P CONTRACT bound-to-mod", "VED U1P OUTS 2"]
  ["sorryAx", "differs", "VED U1P TYPE exact\n", "absent"]
  #vedu1b_both VedBCtl.bs
#vedu1b_expect "B0-axioms" ["VED U1P AXIOMS"] ["sorryAx", "ofReduceBool", "trustCompiler"]
  #vedu1b_probe VedBCtl.bs
#vedu1b_expect "B0-product" ["VED U1 OK VedBCtl.bp.ved_u1", "VED U1P BUNDLE leaves=2", "VED U1P TYPE exact-bundled",
    "VED U1P OUTS 2"] ["differs", "sorryAx"]
  #vedu1b_both VedBCtl.bp
#vedu1b_expect "B0-three-fields" ["VED U1 OK VedBCtl.bs3.ved_u1", "VED U1P BUNDLE leaves=3", "VED U1P TYPE exact-bundled",
    "VED U1P OUTS 3"] ["differs", "sorryAx"]
  #vedu1b_both VedBCtl.bs3
#vedu1b_expect "B0-nested-product" ["VED U1 OK VedBCtl.bpn.ved_u1", "VED U1P BUNDLE leaves=3",
    "VED U1P TYPE exact-bundled", "VED U1P OUTS 3"] ["differs", "sorryAx"]
  #vedu1b_both VedBCtl.bpn
#vedu1b_expect "B0-domain-binder" ["VED U1 OK VedBCtl.bsDom.ved_u1", "VED U1P STMT domains=1", "VED U1P BUNDLE leaves=2",
    "VED U1P TYPE exact-bundled", "VED U1P OUTS 2"] ["differs", "sorryAx"]
  #vedu1b_both VedBCtl.bsDom

/-! ## B1: a constant (single-Signal) declaration keeps today's check -/
#vedu1b_expect "B1-constant" ["VED U1 OK VedBCtl.one.ved_u1", "VED U1P TYPE exact", "VED U1P OUTS 1"]
  ["BUNDLE", "exact-bundled", "differs", "sorryAx"]
  #vedu1b_both VedBCtl.one

/-! ## B2: two fields swapped -/
#eval show CommandElabM Unit from do
  cloneWith `VedBCtl.bs `VedBCtl.bsSw fun xs => do
    let e := app `VedBCtl.bsSw xs
    bundleOf (projOf `VedBCtl.S2.d) (projOf `VedBCtl.S2.s) e
#vedu1b_expect "B2-swapped-fields" ["VED U1P THM theorem", "VED U1P BUNDLE leaves=2", "VED U1P TYPE differs"]
  ["exact-bundled", "TYPE exact\n"]
  #vedu1b_probe VedBCtl.bsSw

/-! ## B3: the bundle of a DIFFERENT declaration (same shape) -/
#eval show CommandElabM Unit from do
  cloneWith `VedBCtl.bs `VedBCtl.bsOther fun xs => do
    -- the statement is about `bs`, not about `bsOther`
    let e := app `VedBCtl.bs xs
    bundleOf (projOf `VedBCtl.S2.s) (projOf `VedBCtl.S2.d) e
#vedu1b_expect "B3-other-declaration" ["VED U1P THM theorem", "VED U1P TYPE differs"] ["exact-bundled"]
  #vedu1b_probe VedBCtl.bsOther

/-! ## B4: product vs structure -/
#eval show CommandElabM Unit from do
  -- the structure declaration's theorem carries the `.1`/`.2` bundle of the product declaration
  cloneWith `VedBCtl.bs `VedBCtl.bsMix fun xs => do
    let e := app `VedBCtl.bp xs
    bundleOf (fun e => mkAppM ``Prod.fst #[e]) (fun e => mkAppM ``Prod.snd #[e]) e
#vedu1b_expect "B4-structure-with-product-bundle" ["VED U1P THM theorem", "VED U1P TYPE differs"] ["exact-bundled"]
  #vedu1b_probe VedBCtl.bsMix
#eval show CommandElabM Unit from do
  -- and the product declaration's theorem carries the structure projections' bundle (of `bs`)
  cloneWith `VedBCtl.bp `VedBCtl.bpMix fun xs => do
    let e := app `VedBCtl.bs xs
    bundleOf (projOf `VedBCtl.S2.s) (projOf `VedBCtl.S2.d) e
#vedu1b_expect "B4-product-with-structure-bundle" ["VED U1P THM theorem", "VED U1P TYPE differs"] ["exact-bundled"]
  #vedu1b_probe VedBCtl.bpMix
