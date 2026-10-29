import Tools.ShippingGen2OneOutTopO
import Tools.ShippingGen2DataBridge
import Tools.ShippingKid
import Tests.Compiler.MemNameCollisionPlainCertTest
set_option autoImplicit false
-- Built at 0efea824 (kjob g2pm4-0efea824: exit 0, standard axioms); audit revised after review (R1 Bool checks, R2 skipped/unexplored listed).
-- No `sorry`, no `axiom`, no `native_decide`.

/-! # P-MEM-4 checks (scripts/gen2/S4_PMEM4_FREEZE.md rev2 §5)

1. **Expected types.** For each of the 14 (original, copy) pairs of the table `pmPairs` below, both types are telescoped;
   the copy's binders must be the original's binders, in the same order, with the same names (macro scopes erased),
   binder infos and types, except that `hnomem` is DELETED (mode `drop`, and `prefix2`) or REPLACED at the same position
   by a binder `hord` whose type is the conclusion of `Tools.ShippingGen2DataBridge.hord_of_row` at the original's
   `ι`/`dom`/`p` (mode `replace`). The copy's binder types are compared after instantiating the copy's foralls with the
   ORIGINAL's fvars. Conclusions: equal (mode `prefix2`: equal to the original's second conjunct `b.body = M.body`).
   Comparison is `==` after `instantiateMVars`; on a syntactic mismatch a `PMEM4 NOTE` line is logged and `isDefEq` is
   the fallback (logged as `PMEM4 DEFEQ`). Any other mismatch: `throwError`. Also: `InstOrigin.child?` occurs in a binder
   type exactly at `hord` of the two top copies and in no binder of the other twelve.
2. **Transitive premise audit** (`pmAuditRoot`): from the TYPE of each root, a breadth-first walk with a visited set and the
   full path of every hit. LOGICAL (unfolded / traversed): definitions whose type ends in `Prop` or in a `Sort`
   (predicates and type formers, e.g. `abbrev Pkgs`), definitions whose type ends in a CLASS (instances, e.g. the
   `Membership` instance behind `∈`), every inductive reached (structures included: the constructor type
   carries the parameters and every field's type; Prop inductives: every constructor type), constructors → their
   inductive. COMPUTATIONAL boundary: a definition whose type ends in neither a sort nor a class (a function / data). Its
   body is scanned (depth/fuel bounded); a forbidden name found there is classified by the boundary definition reached
   on the logical path: if it returns `Bool` it is a BOOL CHECK the premise requires (`f x = true`, `decide`, a data
   row) and counts like a logical hit (`STOP` for the copies); otherwise it is UNCLASSIFIED (needs review), never pure
   and never absence. Definitions not scanned (depth cut, fuel exhausted, opaque inside a body) are UNEXPLORED.
   UNCHECKED boundary (printed, never counted as absence): `opaque` (incl. `partial`), `axiom`, missing declarations,
   Prop/type-level definitions with `@[extern]`/`@[implemented_by]`, classification failures. Theorems (proof terms),
   quotient primitives and recursors met in a type are SKIPPED, each printed with reason and path. Forbidden:
   `Sparkle.Compiler.MachMemory.memChild?`, `Tools.ShippingMemKid.Kid`. A logical or Bool-check hit on any of the 14
   copies is a `STOP`. LOGICAL 0 / BOOLCHECK 0 is NOT a claim that the premises carry no name condition. Fixtures: a
   ≥2-level hidden one (`fxRoot` → `Fx3` (Prop structure) → `Fx2` → `Fx1` → `memChild?`), a direct one, a Bool-check
   NEGATIVE one at one and two Bool levels (`fxCompRoot`, `fxComp2Root`: must be detected), a non-Bool computational one
   (`fxNatRoot`: UNCLASSIFIED), an opaque one;
   positive control: the ORIGINAL `oneOutWidthAt` (its `hnomem`).
3. **Controls**: `hord` holds on the collision data `collPlainCD_D` (where the old premise is provably false,
   `collPlainCD_nomem_false`) — premise level only; `hord` is false on the memory-origin shape `memShape0P` (restated from
   Tests/Gen2/DataBridgeCheck.lean:150-153, not imported); `oneOut_topShipsO` accepts `hord_of_row hrow hsimple` in its
   `hord` slot (`oneOut_topShipsO_of_row`, all other binders universally quantified).
4. `#print axioms` of the 14 copies and the control theorems. -/

namespace Tests.Gen2.PMem4Check
open Lean Meta Elab Command

/-! ## 1. Expected types -/

/-- How a copy's binder list relates to its original's. -/
inductive PMode where
  /-- `hnomem` deleted; same conclusion -/
  | drop
  /-- `hnomem` deleted; conclusion = the original's SECOND conjunct (`core_bodyEq_ranO`) -/
  | prefix2
  /-- `hnomem` replaced at the same position by `hord` (the `hord_of_row` conclusion) -/
  | replace
  deriving BEq, Repr

/-- The 14 pairs (original at 48775f38, copy, mode). -/
def pmPairs : List (Name × Name × PMode) :=
  [(``Tools.ShippingParentTailsA.core_kids_facts_ranA, ``Tools.ShippingParentTailsO.core_bodyEq_ranO, .prefix2),
   (``Tools.ShippingParentTailsA.core_linkedWF_ranA, ``Tools.ShippingParentTailsO.core_linkedWF_ranO, .drop),
   (``Tools.ShippingParentTailsA.core_instOuts_not_assigned_ranA,
      ``Tools.ShippingParentTailsO.core_instOuts_not_assigned_ranO, .drop),
   (``Tools.ShippingParentDesignA.core_hierGate_anyA, ``Tools.ShippingParentDesignO.core_hierGate_anyO, .drop),
   (``Tools.ShippingParentDesignA.core_kidsComb_raw₁A, ``Tools.ShippingParentDesignO.core_kidsComb_raw₁O, .drop),
   (``Tools.ShippingParentDesignA.core_instNames₁A, ``Tools.ShippingParentDesignO.core_instNames₁O, .drop),
   (``Tools.ShippingParentDesignA.core_noSelfRead₁A, ``Tools.ShippingParentDesignO.core_noSelfRead₁O, .drop),
   (``Tools.ShippingParentDesignA.core_outsExtracted₁A, ``Tools.ShippingParentDesignO.core_outsExtracted₁O, .drop),
   (``Tools.ShippingParentDesignA.core_rst_anyA, ``Tools.ShippingParentDesignO.core_rst_anyO, .drop),
   (``Tools.ShippingParentDesignA.core_runFactsHA, ``Tools.ShippingParentDesignO.core_runFactsHO, .drop),
   (``Tools.ShippingGen2.core_callPorts_oneA, ``Tools.ShippingGen2.core_callPorts_oneO, .drop),
   (``Tools.ShippingGen2.core_instOutWidthsOk_oneA, ``Tools.ShippingGen2.core_instOutWidthsOk_oneO, .drop),
   (``Tools.ShippingGen2.oneOutWidthAt, ``Tools.ShippingGen2.oneOutWidthAtO, .replace),
   (``Tools.ShippingGen2.oneOut_topShips, ``Tools.ShippingGen2.oneOut_topShipsO, .replace)]

/-- `==` after `instantiateMVars`; on a mismatch log it and fall back to `isDefEq` (logged); else fail. -/
def pmCheckEq (what : String) (a e : Expr) : MetaM Unit := do
  let a ← instantiateMVars a
  let e ← instantiateMVars e
  if a == e then return
  logInfo m!"PMEM4 NOTE {what}: not syntactically equal, trying isDefEq:{indentExpr a}\nexpected{indentExpr e}"
  if (← isDefEq a e) then
    logInfo m!"PMEM4 DEFEQ {what}: accepted by isDefEq (NOT syntactic)"
  else
    throwError "PMEM4 CHECK FAILED {what}:{indentExpr a}\nexpected{indentExpr e}"

/-- The `hord` type at given `ι`, `dom`, `p`: the conclusion of `hord_of_row` after its five binders
`{ι} {dom} {p} (h) (hf)`. -/
def pmHordTypeFor (ι dom p : Expr) : MetaM Expr := do
  let ci ← getConstInfo ``Tools.ShippingGen2DataBridge.hord_of_row
  unless ci.levelParams.isEmpty do throwError "PMEM4 CHECK FAILED: hord_of_row is universe polymorphic"
  forallBoundedTelescope ci.type (some 5) fun xs body => do
    unless xs.size == 5 do throwError "PMEM4 CHECK FAILED: hord_of_row has {xs.size} < 5 binders"
    let ns ← xs.mapM fun x => return (← x.fvarId!.getDecl).userName
    unless ns == #[`ι, `dom, `p, `h, `hf] do
      throwError "PMEM4 CHECK FAILED: hord_of_row's binders are {ns}, expected [ι, dom, p, h, hf]"
    return body.replaceFVars #[xs[0]!, xs[1]!, xs[2]!] #[ι, dom, p]

/-- The expected-type check of one pair. -/
def pmCheckPair (orig copy : Name) (mode : PMode) : MetaM Unit := do
  let ciO ← getConstInfo orig
  let ciC ← getConstInfo copy
  unless ciO.levelParams == ciC.levelParams do
    throwError "PMEM4 CHECK FAILED {copy}: universe parameters {ciC.levelParams} vs {ciO.levelParams}"
  forallTelescope ciO.type fun xs bodyO => do
    let decls ← xs.mapM (·.fvarId!.getDecl)
    let some idx := decls.findIdx? (·.userName == `hnomem)
      | throwError "PMEM4 CHECK FAILED: the original {orig} has no `hnomem` binder"
    let mut t := ciC.type
    for i in [0:xs.size] do
      if i == idx && mode != .replace then continue
      let dO := decls[i]!
      let .forallE n ty b bi := t
        | throwError "PMEM4 CHECK FAILED {copy}: fewer binders than the original (at original binder {i}, {dO.userName})"
      if i == idx then
        -- mode `replace`: `hord` at the position of `hnomem`
        unless n.eraseMacroScopes == `hord do
          throwError "PMEM4 CHECK FAILED {copy}: binder {i} is {n}, expected hord"
        unless bi == .default do throwError "PMEM4 CHECK FAILED {copy}: hord is not explicit"
        let find (s : Name) : MetaM Expr := do
          match decls.find? (·.userName == s) with
          | some d => pure (mkFVar d.fvarId)
          | none => throwError "PMEM4 CHECK FAILED: {orig} has no binder {s}"
        let exp ← pmHordTypeFor (← find `ι) (← find `dom) (← find `p)
        pmCheckEq s!"{copy} binder hord" ty exp
        if b.hasLooseBVar 0 then throwError "PMEM4 CHECK FAILED {copy}: a later binder depends on hord"
        t := b.lowerLooseBVars 1 1
      else
        unless n.eraseMacroScopes == dO.userName.eraseMacroScopes do
          throwError "PMEM4 CHECK FAILED {copy}: binder {i} is named {n}, the original's is {dO.userName}"
        unless bi == dO.binderInfo do
          throwError "PMEM4 CHECK FAILED {copy}: binder {n} has a different binder info"
        pmCheckEq s!"{copy} binder {n}" ty dO.type
        t := b.instantiate1 xs[i]!
    let expC ← match mode with
      | .prefix2 => do
        let some (_, r) := bodyO.and? | throwError "PMEM4 CHECK FAILED: {orig}'s conclusion is not a conjunction"
        let some (c2, _) := r.and? | throwError "PMEM4 CHECK FAILED: {orig}'s conclusion has < 3 conjuncts"
        pure c2
      | _ => pure bodyO
    pmCheckEq s!"{copy} conclusion" t expC
  logInfo m!"PMEM4 TYPE OK {copy} ({repr mode}) against {orig}"

/-- The names of the binders (conclusion binders included) whose type mentions `c`. -/
def pmBindersMentioning (thm c : Name) : MetaM (List Name) := do
  let ci ← getConstInfo thm
  forallTelescope ci.type fun xs _ => do
    let mut r : List Name := []
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.type.getUsedConstants.contains c then r := r ++ [d.userName.eraseMacroScopes]
    return r

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  unless pmPairs.length == 14 do throwError "PMEM4 CHECK FAILED: {pmPairs.length} pairs, expected 14"
  for (o, c, m) in pmPairs do
    pmCheckPair o c m
  for (_, c, m) in pmPairs do
    let ms ← pmBindersMentioning c ``Sparkle.Compiler.MachInstOrigin.InstOrigin.child?
    let exp : List Name := if m == .replace then [`hord] else []
    unless ms == exp do
      throwError "PMEM4 CHECK FAILED {c}: binders mentioning InstOrigin.child? are {ms}, expected {exp}"
  logInfo m!"PMEM4 TYPES OK: 14 pairs; InstOrigin.child? only in hord of the two top copies"

/-! ## 2. Transitive premise audit -/

/-- The forbidden names (resolved at elaboration of this file: both exist). -/
def pmForbidden : List Name := [``Sparkle.Compiler.MachMemory.memChild?, ``Tools.ShippingMemKid.Kid]

/-- What the walk found for one root. -/
structure PAudit where
  /-- forbidden names reached on the LOGICAL path (full path root → … → name) -/
  logical : Array (List Name) := #[]
  /-- forbidden names reached inside the body of a computational definition whose result is `Bool` and that is
  reached on the logical path: a Bool check the premise requires (`f x = true`, `decide`, a data row). Counted as a
  name-exclusion condition: a `STOP` for the 14 copies, like `logical` -/
  boolcheck : Array (List Name) := #[]
  /-- forbidden names reached inside the body of a NON-Bool computational definition reached on the logical path:
  UNCLASSIFIED (needs review): the premise may or may not constrain names through it; never counted as absence -/
  computational : Array (List Name) := #[]
  /-- computational constants NOT scanned (depth cut or fuel exhausted): UNEXPLORED, never counted as absence -/
  unexplored : Array (List Name × String) := #[]
  /-- computational boundary constants met on the logical path (not unfolded logically) -/
  compNames : Array Name := #[]
  /-- unchecked boundaries on the logical path (never counted as absence) -/
  unchecked : Array (List Name × String) := #[]
  /-- skipped with a note and the path by which they were reached (all printed) -/
  skipped : Array (List Name × String) := #[]
  /-- logical constants unfolded / traversed (Prop and type-level definitions, class instances, inductives) -/
  unfolded : Nat := 0
  visited : Nat := 0
  compTruncated : Bool := false
  deriving Inhabited

/-- What a definition's type ends in (after `forallTelescopeReducing` and `whnf`). -/
inductive PKind where
  /-- a sort: a predicate (`Prop`) or a type former — LOGICAL, unfolded -/
  | sort
  /-- an application of a class: an instance (e.g. the `Membership` behind `∈`) — LOGICAL, unfolded -/
  | inst
  /-- anything else: data or a function — COMPUTATIONAL boundary -/
  | comp
  deriving BEq, Repr

def pmResultKind (ty : Expr) : MetaM PKind :=
  forallTelescopeReducing ty fun _ b => do
    let b ← whnf b
    match b with
    | .sort _ => return .sort
    | _ =>
      match b.getAppFn.constName? with
      | some h => return (if Lean.isClass (← getEnv) h then .inst else .comp)
      | none => return .comp

def pmResultKindSafe (ty : Expr) : MetaM (Except String PKind) := do
  try
    return .ok (← pmResultKind ty)
  catch e =>
    return .error (← e.toMessageData.toString)

/-- Does a definition's type end in `Bool` (after `forallTelescopeReducing` and `whnf`)? -/
def pmResultIsBool (ty : Expr) : MetaM Bool := do
  try
    forallTelescopeReducing ty fun _ b => do
      let b ← whnf b
      return b.isConstOf ``Bool
  catch _ => return false

def pmPath (p : List Name) : String := " → ".intercalate (p.map toString)

/-- The transitive audit of one root (see the module doc, item 2). -/
def pmAuditRoot (forb : List Name) (root : Name) (maxVisit : Nat := 400000) (compDepth : Nat := 3)
    (compFuel : Nat := 40000) : MetaM PAudit := do
  let env ← getEnv
  let some rci := env.find? root | throwError "PMEM4 AUDIT FAILED: root {root} not found"
  let mut out : PAudit := {}
  let mut seen : NameSet := {}
  let mut queue : Array (Name × List Name) := #[]
  for c in rci.type.getUsedConstants do
    queue := queue.push (c, [root])
  let mut comps : Array (Name × List Name × Bool) := #[]
  let mut i := 0
  while i < queue.size do
    let (c, path) := queue[i]!
    i := i + 1
    if seen.contains c then continue
    seen := seen.insert c
    out := { out with visited := out.visited + 1 }
    if out.visited > maxVisit then
      throwError "PMEM4 AUDIT INCOMPLETE at {root}: more than {maxVisit} logical constants; absence NOT established"
    let here := path ++ [c]
    if forb.contains c then
      out := { out with logical := out.logical.push here }
      continue
    match env.find? c with
    | none => out := { out with unchecked := out.unchecked.push (here, "no declaration") }
    | some (.axiomInfo _) => out := { out with unchecked := out.unchecked.push (here, "axiom") }
    | some (.opaqueInfo _) => out := { out with unchecked := out.unchecked.push (here, "opaque/partial") }
    | some (.thmInfo _) =>
      out := { out with skipped := out.skipped.push (here, "theorem (a proof term) inside a type: its statement is not a premise of the root") }
    | some (.quotInfo _) => out := { out with skipped := out.skipped.push (here, "quotient primitive (Quot/Quot.mk/Quot.lift/Quot.ind: no body)") }
    | some (.recInfo _) =>
      out := { out with skipped := out.skipped.push (here, "recursor (no body; its motive/minor premises are in the walked term)") }
    | some (.ctorInfo cv) =>
      unless seen.contains cv.induct do queue := queue.push (cv.induct, here)
    | some (.inductInfo iv) =>
      -- every inductive reached on the logical path: its type, its mutual block, every constructor type
      -- (for a structure: the parameters and every field's type)
      out := { out with unfolded := out.unfolded + 1 }
      let mut cs := iv.type.getUsedConstants
      for n in iv.all do cs := cs.push n
      for k in iv.ctors do
        let kci ← getConstInfo k
        cs := cs ++ kci.type.getUsedConstants
      for d in cs do
        unless seen.contains d do queue := queue.push (d, here)
    | some (.defnInfo dv) =>
      match (← pmResultKindSafe dv.type) with
      | .error msg => out := { out with unchecked := out.unchecked.push (here, s!"classification failed: {msg}") }
      | .ok .comp =>
        -- a computational definition: boundary, scanned below for reporting only
        out := { out with compNames := out.compNames.push c }
        comps := comps.push (c, here, ← pmResultIsBool dv.type)
      | .ok _ =>
        -- `.sort` (predicate / type former) or `.inst` (class instance): LOGICAL
        if Lean.isExtern env c || (Lean.Compiler.implementedByAttr.getParam? env c).isSome then
          out := { out with unchecked := out.unchecked.push (here, "Prop/type-level definition with extern/implemented_by") }
        else
          out := { out with unfolded := out.unfolded + 1 }
          for d in dv.type.getUsedConstants ++ dv.value.getUsedConstants do
            unless seen.contains d do queue := queue.push (d, here)
  -- the computational boundary: depth/fuel-bounded scan of the bodies. A hit under a Bool-valued boundary definition is a
  -- BOOL CHECK (a name condition the premise requires); under any other one it is UNCLASSIFIED (needs review). What is
  -- not scanned (depth cut, fuel exhausted) is UNEXPLORED. The two classes are scanned separately (a definition reached
  -- under both is scanned under both).
  let mut cseenB : NameSet := {}
  let mut cseenC : NameSet := {}
  let mut cq : Array (Name × List Name × Nat × Bool) := comps.map fun (c, p, b) => (c, p, 0, b)
  let mut j := 0
  let mut fuel := compFuel
  while j < cq.size do
    let (c, p, dep, isB) := cq[j]!
    j := j + 1
    if (if isB then cseenB.contains c else cseenC.contains c) then continue
    if fuel == 0 then
      out := { out with compTruncated := true,
                        unexplored := out.unexplored.push (p, "computational fuel exhausted") }
      continue
    fuel := fuel - 1
    if isB then cseenB := cseenB.insert c else cseenC := cseenC.insert c
    match env.find? c with
    | some (.defnInfo dv) =>
      for d in dv.value.getUsedConstants do
        if forb.contains d then
          if isB then out := { out with boolcheck := out.boolcheck.push (p ++ [d]) }
          else out := { out with computational := out.computational.push (p ++ [d]) }
        else if (if isB then cseenB.contains d else cseenC.contains d) then
          pure ()
        else if dep < compDepth then
          cq := cq.push (d, p ++ [d], dep + 1, isB)
        else
          match env.find? d with
          | some (.defnInfo _) => out := { out with unexplored := out.unexplored.push (p ++ [d], s!"computational depth cut at {compDepth}") }
          | some (.opaqueInfo _) => out := { out with unexplored := out.unexplored.push (p ++ [d], "opaque/partial inside a computational body") }
          | _ => pure ()
    | some (.opaqueInfo _) => out := { out with unexplored := out.unexplored.push (p, "opaque/partial inside a computational body") }
    | _ => pure ()
  return out

/-- Print one root's audit. -/
def pmReport (root : Name) (a : PAudit) : MetaM Unit := do
  logInfo m!"PMEM4 AUDIT {root}: logical constants unfolded {a.unfolded} (visited {a.visited}); LOGICAL hits {a.logical.size}; BOOLCHECK hits {a.boolcheck.size}; UNCLASSIFIED computational hits {a.computational.size}; computational boundary names {a.compNames.size}; UNCHECKED boundaries {a.unchecked.size}; UNEXPLORED {a.unexplored.size}; skipped {a.skipped.size}{if a.compTruncated then " (computational fuel exhausted)" else ""}"
  for p in a.logical do logInfo m!"PMEM4 LOGICAL HIT {root}: {pmPath p}"
  for p in a.boolcheck do logInfo m!"PMEM4 BOOLCHECK HIT {root}: {pmPath p}"
  for p in a.computational do logInfo m!"PMEM4 UNCLASSIFIED HIT {root} (needs review): {pmPath p}"
  for (p, why) in a.unchecked do logInfo m!"PMEM4 UNCHECKED {root} ({why}): {pmPath p}"
  for (p, why) in a.unexplored do logInfo m!"PMEM4 UNEXPLORED {root} ({why}): {pmPath p}"
  for (p, why) in a.skipped do logInfo m!"PMEM4 SKIPPED {root} ({why}): {pmPath p}"

/-! ### Fixtures -/

/-- one level: the forbidden name in the Prop definition -/
def Fx1 : Prop := ∀ c : Lean.Name, Sparkle.Compiler.MachMemory.memChild? c = none
/-- two levels: a Prop definition hiding `Fx1` -/
def Fx2 : Prop := Fx1
/-- three levels: a Prop structure whose field is `Fx2` -/
structure Fx3 : Prop where
  h : Fx2
/-- the hidden fixture root: the forbidden name is three unfoldings away -/
theorem fxRoot (_h : Fx3) : True := trivial
/-- the direct fixture root -/
theorem fxDirect (_h : ∀ c : Lean.Name, Sparkle.Compiler.MachMemory.memChild? c = none) : True := trivial
/-- NEGATIVE fixture: a name-exclusion condition hidden in a Bool check (`fxComp a = true` requires `memChild? a = none`);
it MUST be detected as a BOOLCHECK hit (not passed as computational-only) -/
def fxComp (c : Lean.Name) : Bool := (Sparkle.Compiler.MachMemory.memChild? c).isNone
theorem fxCompRoot (_h : fxComp `a = true) : True := trivial
/-- the same check one Bool wrapper deeper -/
def fxComp2 (c : Lean.Name) : Bool := fxComp c && true
theorem fxComp2Root (_h : fxComp2 `a = true) : True := trivial
/-- a NON-Bool computational use: `memChild?` inside a `Nat`-valued function. The audit cannot tell whether the premise
constrains names through it; it must be reported as UNCLASSIFIED (needs review), neither as logical nor as pure -/
def fxNat (c : Lean.Name) : Nat := ((Sparkle.Compiler.MachMemory.memChild? c).map (fun _ => 1)).getD 0
theorem fxNatRoot (_h : fxNat `a ≤ 7) : True := trivial
/-- an opaque Prop: the walk cannot see inside -/
opaque FxOp : Prop
theorem fxOpRoot (_h : FxOp) : True := trivial

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  for f in pmForbidden do
    unless (← getEnv).contains f do throwError "PMEM4 AUDIT FAILED: forbidden name {f} is not in the environment"
  -- the hidden fixture MUST be detected, with its full path
  let a ← pmAuditRoot pmForbidden ``fxRoot
  pmReport ``fxRoot a
  unless a.logical.any (· == [``fxRoot, ``Fx3, ``Fx2, ``Fx1, ``Sparkle.Compiler.MachMemory.memChild?]) do
    throwError "PMEM4 AUDIT FAILED: the hidden fixture fxRoot → Fx3 → Fx2 → Fx1 → memChild? is NOT detected"
  let a ← pmAuditRoot pmForbidden ``fxDirect
  pmReport ``fxDirect a
  unless a.logical.any (· == [``fxDirect, ``Sparkle.Compiler.MachMemory.memChild?]) do
    throwError "PMEM4 AUDIT FAILED: the direct fixture is NOT detected"
  -- the Bool-check fixture (negative): MUST be detected as a BOOLCHECK hit, also one Bool wrapper deeper
  let a ← pmAuditRoot pmForbidden ``fxCompRoot
  pmReport ``fxCompRoot a
  unless a.boolcheck.any (· == [``fxCompRoot, ``fxComp, ``Sparkle.Compiler.MachMemory.memChild?]) do
    throwError "PMEM4 AUDIT FAILED: the Bool-check fixture fxCompRoot → fxComp → memChild? is NOT detected"
  let a ← pmAuditRoot pmForbidden ``fxComp2Root
  pmReport ``fxComp2Root a
  unless a.boolcheck.any (· == [``fxComp2Root, ``fxComp2, ``fxComp, ``Sparkle.Compiler.MachMemory.memChild?]) do
    throwError "PMEM4 AUDIT FAILED: the 2-level Bool-check fixture fxComp2Root → fxComp2 → fxComp → memChild? is NOT detected"
  -- the non-Bool computational fixture: UNCLASSIFIED (needs review), not a Bool check, not logical
  let a ← pmAuditRoot pmForbidden ``fxNatRoot
  pmReport ``fxNatRoot a
  unless a.logical.isEmpty && a.boolcheck.isEmpty do
    throwError "PMEM4 AUDIT FAILED: the non-Bool computational fixture was classified as logical/boolcheck"
  unless a.computational.any (· == [``fxNatRoot, ``fxNat, ``Sparkle.Compiler.MachMemory.memChild?]) do
    throwError "PMEM4 AUDIT FAILED: the non-Bool computational use fxNatRoot → fxNat → memChild? is not reported as UNCLASSIFIED"
  -- an opaque Prop is an UNCHECKED boundary
  let a ← pmAuditRoot pmForbidden ``fxOpRoot
  pmReport ``fxOpRoot a
  unless a.unchecked.any (·.1 == [``fxOpRoot, ``FxOp]) do
    throwError "PMEM4 AUDIT FAILED: the opaque fixture is not reported as an unchecked boundary"
  -- positive control: the ORIGINAL `oneOutWidthAt` (its `hnomem` names `memChild?`)
  let a ← pmAuditRoot pmForbidden ``Tools.ShippingGen2.oneOutWidthAt
  pmReport ``Tools.ShippingGen2.oneOutWidthAt a
  unless a.logical.any (· == [``Tools.ShippingGen2.oneOutWidthAt, ``Sparkle.Compiler.MachMemory.memChild?]) do
    throwError "PMEM4 AUDIT FAILED: the original oneOutWidthAt's hnomem is NOT detected (the auditor misses the name half)"
  logInfo m!"PMEM4 AUDIT FIXTURES OK: hidden (4 levels), direct, Bool check (1 and 2 levels, detected), non-Bool computational (UNCLASSIFIED), opaque, original oneOutWidthAt"

set_option maxHeartbeats 0 in
run_cmd liftTermElabM do
  let mut stops : Array String := #[]
  let mut uncl : Nat := 0
  for (_, c, _) in pmPairs do
    let a ← pmAuditRoot pmForbidden c
    pmReport c a
    for p in a.logical do stops := stops.push s!"LOGICAL {pmPath p}"
    for p in a.boolcheck do stops := stops.push s!"BOOLCHECK {pmPath p}"
    uncl := uncl + a.computational.size
  unless stops.isEmpty do
    throwError "STOP: a forbidden name is reached on the LOGICAL path or in a Bool check of a P-MEM-4 copy (report, do not patch):\n{"\n".intercalate stops.toList}"
  logInfo m!"PMEM4 AUDIT RESULT: LOGICAL 0 and BOOLCHECK 0 in the 14 copies; UNCLASSIFIED hits {uncl} (printed above, need review). This is NOT a claim that the premises carry no name condition: UNCHECKED, UNEXPLORED and SKIPPED items printed above are not absence"

end Tests.Gen2.PMem4Check

/-! ## 3. Controls -/

namespace Tests.Gen2.PMem4Check
open Sparkle.Tests.Compiler.MemNameCollisionPlainCertTest (collPlainCD_D)

/-- **Positive (premise level)**: on the collision data, where the old premise is FALSE
(`collPlainCD_nomem_false`), the origin premise `hord` holds (form of `hord_of_row`'s conclusion). -/
theorem collPlainCD_hord : ∀ (k : Nat) (hk : k < collPlainCD_D.shape.insts.length),
    (collPlainCD_D.shape.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none := by
  intro k hk
  have hall : ∀ o ∈ collPlainCD_D.shape.instTagged, o.2.child?.isNone = true := by
    first | decide | decide +kernel
  exact Tools.ShippingChildInv.notag_at hall hk

/-- the old premise is false there (re-stated use of the existing control) -/
example : ¬ (∀ x ∈ collPlainCD_D.shape.instTagged, x.2.child?.isNone = true ∧
    (Sparkle.Compiler.MachMemory.memChild? x.1).isNone = true) :=
  Sparkle.Tests.Compiler.MemNameCollisionPlainCertTest.collPlainCD_nomem_false

/-- `memShape0` of Tests/Gen2/DataBridgeCheck.lean:150-153, restated (that file is not imported): one call entry with a
MEMORY origin and no field list. -/
def memShape0P : Sparkle.Compiler.Elab.MachineShape :=
  { binders := [], body := .bvar 0,
    layout := { slots := [], outs := [], resetKind := .synchronous },
    insts := [(`m, [], .bits 8)], instOrigins := [.mem false 4 8] }

/-- **Negative**: `hord` is false on a memory-origin entry, so the `O` tops do not apply to it. -/
theorem memShape0P_hord_false : ¬ ∀ (k : Nat) (hk : k < memShape0P.insts.length),
    (memShape0P.instOrigins.getD k Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child? = none := by
  intro h
  have h0 := h 0 (by first | decide | simp [memShape0P])
  have hs : (memShape0P.instOrigins.getD 0 Sparkle.Compiler.MachInstOrigin.InstOrigin.ord).child?.isSome = true := by
    first | rfl | decide
  rw [h0] at hs
  first | (simp at hs) | (cases hs) | exact absurd hs (by decide)

end Tests.Gen2.PMem4Check

/-! ### Composition: `hord_of_row` fills the `hord` slot (ambient: as OneOutTop:260-283) -/
namespace Tools.ShippingGen2
open Lean hiding Module Expr
open Meta Sparkle.Compiler.Elab Sparkle.IR.AST Sparkle.IR.Semantics Sparkle.IR.Machine
open Sparkle.IR.AST (Module)
open Sparkle.IR.OptCheck Sparkle.IR.RefineCheck Sparkle.IR.HierCheck
open Sparkle.IR.RegDedup (declWidth isAssign)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal
open Tools.ShippingHierOpen Tools.ShippingHierState Tools.ShippingHierStateG
open Tools.ShippingEntrySoundness Tools.ShippingMixedSourceBridge
open Tools.ShippingMachineEntry Tools.ShippingMachineAuto
open Tools.ShippingMachineLinked Tools.ShippingMachineDepth
open Tools.ShippingSeqOptSoundness (seedIn)
open Tools.ShippingMachineSource Tools.ShippingMachineDenote
open Tools.ShippingQuadComposed (GenFacts)
open Tools.ShippingMachineShipsDepth (ResetNk)
open Tools.ShippingMachineCallsLinkedT (valsOf MemFacts)
open Tools.ShippingMachineChild (InRange boolsOf bitsOf)
open Tools.ShippingChildInvA (RefLawsAOps RefLawsATele AdmCtx)
open Tools.ShippingChildCacheA (RealChildA JQC)
open Tools.ShippingChildRunAKids Tools.ShippingChildRunAMain
open Tools.ShippingChildBndCore (cv dv)

variable {ι : Type} {dom : ι → DomainConfig}
variable {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}

/-- **Composition control**: `oneOut_topShipsO` with its `hord` slot filled by `hord_of_row hrow hsimple` (the P-MEM row
of the package); every other binder of `oneOut_topShipsO` universally quantified, in its order. -/
theorem _root_.Tests.Gen2.PMem4Check.oneOut_topShipsO_of_row (L : Laws mref cref) (P : Pkgs ι dom) (p : Pkg ι dom)
    {mctx : Meta.Context} {cctx : Core.Context} {w w1 : Void IO.RealWorld} {raw b : Sparkle.IR.AST.Module} {D : Design}
    (hdata : MemParentDataOk p)
    (hrow : Tools.ShippingGen2DataBridge.OneOutNoMemRow p = true)
    (hins : p.d.shape.insts ≠ []) (hsimple : p.d.shape.instFields = []) (hsl : p.d.shape.layout.slots ≠ [])
    (hA : AdmCtx L.O.quiet mctx cctx)
    (hcore : RunsTo (synthesizeCombinationalCore p.decl [] false) mctx mref cctx cref w (raw, D) w1)
    (hpost : b = Sparkle.IR.ZeroWidth.dropZeroWidthModule raw ∨
      b = mergeChecked (Sparkle.IR.ZeroWidth.dropZeroWidthModule raw))
    (entry : MachineDefines mctx mref cctx cref p.decl p.d.shape)
    (ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D)
    (hdec : ∀ k (hk : k < p.d.shape.insts.length), ∃ q, P (p.d.shape.insts[k]).1 = some q ∧ CallDec p q k)
    (h : Tools.ShippingMachineTraceX.MachineTraceLBX (ServedP (ShipsRes L P) p.decl p.d.shape raw D)
      p.decl p.d raw D dom p.src p.extS p.extBS p.lsrc)
    (hW : ∀ k, OneOutWidth P p k)
    (n : Nat) :
    TopShips p (n + 1) p.decl b raw D :=
  oneOut_topShipsO L P p hdata (Tools.ShippingGen2DataBridge.hord_of_row hrow hsimple) hins hsimple hsl hA hcore
    hpost entry ran hdec h hW n

end Tools.ShippingGen2

/-! ## 4. Axioms -/

-- the 14 copies
#print axioms Tools.ShippingParentTailsO.core_bodyEq_ranO
#print axioms Tools.ShippingParentTailsO.core_linkedWF_ranO
#print axioms Tools.ShippingParentTailsO.core_instOuts_not_assigned_ranO
#print axioms Tools.ShippingParentDesignO.core_hierGate_anyO
#print axioms Tools.ShippingParentDesignO.core_kidsComb_raw₁O
#print axioms Tools.ShippingParentDesignO.core_instNames₁O
#print axioms Tools.ShippingParentDesignO.core_noSelfRead₁O
#print axioms Tools.ShippingParentDesignO.core_outsExtracted₁O
#print axioms Tools.ShippingParentDesignO.core_rst_anyO
#print axioms Tools.ShippingParentDesignO.core_runFactsHO
#print axioms Tools.ShippingGen2.core_callPorts_oneO
#print axioms Tools.ShippingGen2.core_instOutWidthsOk_oneO
#print axioms Tools.ShippingGen2.oneOutWidthAtO
#print axioms Tools.ShippingGen2.oneOut_topShipsO
-- the controls
#print axioms Tests.Gen2.PMem4Check.collPlainCD_hord
#print axioms Tests.Gen2.PMem4Check.memShape0P_hord_false
#print axioms Tests.Gen2.PMem4Check.oneOut_topShipsO_of_row
