# DC-CONNECT: DeclConnect on the actual source — abstract core (accepted scope) + Part C complete-type freeze for review (rev5)

Issue `sparkle-gen5-dc-connect` (parent `sparkle-gen5-decl-bridge`; units DC-FORM / DC-SUPPLY / DG-DECLCONNECT).
Base: `kjob/g5dc-r3` 08e97dba (abstract U1-U6 and check rev3: scoped approved by the reviewer; Part C reported as unfrozen, which was correct).
Design sources (read with `git show par/gen5-t2:...`, c398021c): `DGEN_FREEZE.md` rev2 §2.6 (cited `DGEN:§2.6`), `T2COVER_FREEZE.md` rev2 §2,
`DG_ENV_FREEZE.md` rev2.2, and `scripts/gen2/GENERAL_SPEC.md` (FG §1.1 lines 88-93, M5 lines 488-507, §6 table line 535).

**Revision rev5 (this revision; answers the reviewer's `changes_requested` on rev4 335817c3).** Docs part: R1-R3 below. Lean part (committed separately,
agent build only, NOT a clean issue-linked build): U-UNIV (`Tools/ShippingGen5DeclConnectAbs.lean` `variable` line only), U-SHAPE1/U-SHAPE2/U-ROWS
(`Tools/ShippingGen5DeclConnect.lean`, new file) and the audit `Tests/Gen5/DeclConnectCheck.lean` (§C.8, built SHA 68f1be34). `FG_COMPLETE` and `ConstValueE`
are NOT in Lean: R1 changes the `FG_COMPLETE` statement and awaits approval of §C.3 rev5.
- **R1** (§C.3): the rev4 `FG_COMPLETE` is a *conditional schema*. With `Post = False`, or `GP = none`, or `CV` empty the raw/package/DeclConnect parts hold vacuously, and a
  functionality statement holds for an empty `CV`. rev5 separates the conditional schema (`FG_COND`) from the final connection (`FG_CONNECT`), which adds an explicit
  obligation: for the SAME real entry witness there is a `raw` with `Post b raw` and a package `GP env₀ declName = some p`. While M4's `Post`/`ReflectsAll` are not defined in Lean
  the whole is an INTERMEDIATE (parametrized) statement and is not called complete.
- **R2** (§C.6): a prim table that is functional in `Name` does NOT by itself give `ConstValueFunctional` (a `const-unfold` derivation and a `const-prim` derivation for the same `Name`
  may both exist). The rules, the exclusivity/consistency condition and the functionality proof are PLANNED, not claimed. It is not established that a new TRUSTED boundary is required;
  the decision document is rewritten on that basis (no decision is asked at this stage).
- **R3** (§C.3, §C.8): the R-G `TopShips` strengthens the no-clock/no-reset guarantee (its premises are weaker, so the conclusion covers more runs); rev4 said "weaker". An `inferType`
  comparison cannot see a change of `TopShips`' body; the check pins the body/pair of the contract, or the contract is explicitly tied to the existing R-G audit (§C.3).
- The Bool observation mutant of rev4 (an identity on a `Bool` result) was ill-typed against a `Nat` result; the audit uses well-typed changes (§C.8).

**Revision rev4 (previous; docs only).** Part C is rewritten as a complete-type freeze PROPOSAL for review.
The old §1.1-§1.3, §2, §3 and §4a of rev3 are replaced by §C.1-§C.8 below; Part A (§4, §4.1, the accepted abstract core) is kept verbatim.
What rev4 does, against the six asks of the brief:
1. `FG_COMPLETE` is bound from the Lean text: every binder type is copied from a named file:line, and the statement was elaborated against the real
   constants in a LOCAL scratch file (§C.3, §C.1 "how this was checked"). Three FG ingredients turned out to have NO Lean definition in this
   survey (`ReflectsAll`, the `b`↔`raw` relation, `Pk`); they are explicit owner-premises, not placeholders (§C.3).
   TopShips is stated for the S2 version (`kjob/g2tc-s2` fa84af5d, R-G, in review); the difference to the base version is recorded (§C.3).
2. `DataSoundAt`'s third conjunct is DG-DATAOF rev1's `initOk` in its real type (§C.4). No placeholder remains.
3. `genP`/`entry₀`/`CallEdge`/`GenData`/`ordCallees`/`genData₀`/`GenWF`/`GenIn` use the names and argument orders of DG-SEM U3 (4ebc4067) and
   DG-ACC freeze rev0 (c5b9140c); rev3's own `GenPInv` is DELETED, not redefined (§C.5).
4. `SigShape`/`sigShape?`/`SigShape.applyArgs`/`obs`/`ResShape.obs`/`outPorts` have complete Lean bodies, elaborated in scratch; the instance
   connection to the abstract `Match/Obs/shapeOf` is complete and has one consequence for Part A: its `Pk : Type` must become `Pk : Type u`
   (`Pkg ι dom : Type 1`), unit U-UNIV (§C.2, §C.8).
5. `ConstValue`: the part that is a plain definition and the part that is a name-keyed table are separated (§C.6). The table is a candidate new
   TRUSTED boundary; a decision document is in `scripts/gen5/DC_CONNECT_PRIM_TABLE_DECISION.md`. NOT adopted here.
6. Supplier table and the unit/audit plan (§C.7, §C.8).

Earlier revisions: rev3 answered review R1-R3 on b99edb6b (audit/doc only). rev2 answered R1-R3 on rev1 (08293159).

## Acceptance scope (rev4)

| part | content | status |
|---|---|---|
| **A. Accepted abstract core** | §4 U1-U6 in `Tools/ShippingGen5DeclConnectAbs.lean` and the audit `Tests/Gen5/DeclConnectAbsCheck.lean` | Lean written; clean issue-linked build dc3v-08e97dba exit 0; scoped approved at 08e97dba. Abstract; says nothing about the actual source. U-UNIV (universe of `Pk` only, proofs unchanged) is implemented at cef857c6 (agent build; the audit re-run passes: TYPE 8, MUTANT 8, U-UNIV, AXIOMS 8, CLOSURE 8 + controls); it is an edit of an accepted file and awaits the clean build and review |
| **C. Concrete design: complete-type freeze PROPOSAL** | §C.1-§C.8 | §C.2 (shape vocabulary, recognizer, agreement lemmas, `DeclConnect` instance, conditional rows) is now Lean in `Tools/ShippingGen5DeclConnect.lean` + `Tests/Gen5/DeclConnectCheck.lean` (agent build 68f1be34, exit 0, no `sorry`, standard axioms only; clean issue-linked build is the coder's). §C.3 (`FG_COND`/`FG_CONNECT`), §C.4, §C.5, §C.6 stay design text; no Lean |

Reading rule: Part A can stay accepted without Part C. Part C §C.3-§C.6 are the object of the freeze review. The §C.2 Lean was written in parallel, as the brief of this revision
allows (U-UNIV, §C.2 adapter/recognizer/agreement lemmas, conditional U-ROWS only); nothing of §C.3-§C.6 is in Lean.

Wording rules used throughout:
- "not supplied" / "this survey found no source or route" is a statement about THIS survey. It is not a claim that something is impossible or underivable.
- A "mutant" is a rejection by signature or defeq of a changed statement. It is not a semantic counterexample.
- Nothing here is a new TRUSTED boundary, law, FG or guarantee change, compiler change, or edit of shared definitions (`Tools/ShippingGen2Defs.lean`,
  `T1Hyp`, `T1HypND`, `Elab*.lean`). What would need one is in §C.6 / the decision document and is NOT adopted.
- New Lean goes in NEW files only: `Tools/ShippingGen5DeclConnectAbs.lean` (exists, Part A; U-UNIV edits only its `variable` line) and later
  `Tools/ShippingGen5DeclConnect.lean` (+ `lean_lib` entries), checks `Tests/Gen5/DeclConnectAbsCheck.lean`, `Tests/Gen5/DeclConnectCheck.lean`.

## 0. What is and is not in scope

| item | status |
|---|---|
| (1) types of `DeclConnect`, `SigShape`, `sigShape?`, `ShapeMatches`, `FG_COMPLETE`, `DataSoundAt`; dependencies as PREMISES | §C.2-§C.5, complete-type proposal |
| (2) table of what the actual source side supplies | §C.7 |
| (3) insertion point in FG and the check that FG is not shrunk | §C.3 |
| (4) pure lemma units that do not depend on DG-SEM / DG-DATAOF / DG-ACC / DG-COVER | Part A (§4, built) and §C.8 (concrete, not yet written) |
| (5) `ConstValue` formulation | §C.6 classification; the inductive `ConstValueE` itself is a later freeze (DCF); a trusted table is a user item |
| final connection that USES the dependencies' results | `declConnect_of_rows` (§4 U6, abstract, INTERMEDIATE) takes `hstep`; NOT completion |

Completion of this issue's goal is `FG-REF ∧ ConstValueOk ∧ DeclConnect env₀ (genP env₀) Tgt` (DGEN:§2.6). Neither defining `ConstValue`, nor
`DeclConnectImp`, nor `ConstValueOk` alone, nor `DeclConnect` for a `Tgt` narrower than all successful targets completes it. This freeze completes none of those.

## C.0 The rev3 gap list, row by row (what rev4 fills and what it hands to an owner)

| rev3 gap | rev4 | where | remaining owner-premise (stated, not a placeholder) |
|---|---|---|---|
| `FG_COMPLETE`: `b : Bool` | `b : Sparkle.IR.AST.Module` | §C.3 | none |
| `FG_COMPLETE`: `D` type | `D : Sparkle.IR.AST.Design` | §C.3 | none |
| `FG_COMPLETE`: `raw` unbound | bound by `∀ raw, Post b raw → …`, `Post` an explicit parameter | §C.3 | `Post` = M4's "`b ↔ raw` of the default entry's two post-processing steps" (GENERAL_SPEC.md:100, 481): no Lean definition found |
| `Start`/`RunsTo`/`Laws`/`envAt`/`ReflectsAll` argument lists | `Start`, `RunsTo`, `Laws`, `envAt`, `synthesizeCombinational*`, `TopShips` copied from file:line and elaborated; `ReflectsAll` has NO Lean definition found, so it is a parameter with the type FG's use fixes | §C.3 | `ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop` (GENERAL_SPEC.md:92, 98: "fixed in M4") |
| `Pk` of FG | `GP : Environment → Pkgs ι dom`, to be `fun env₀ => genP (K env₀) (hF env₀)` | §C.3, §C.5 | DG-ACC `genP`, `AssignKit`, `GenSFacts` |
| `DataSoundAt` third conjunct | `p.d.initOk (initsOf p.d) = true` with DG-DATAOF's `initsOf` | §C.4 | DG-DATAOF `initsOf` (kjob/g5do-r2 8d20ae99, Tools/ShippingGen5DataOfPure.lean:354) |
| `SigShape.applyArgs`, `ResShape.obs`, `SigShape.obs`, `sigShape?`, `ResShape.outPorts` | complete Lean bodies; `ResShape.outPorts` is now declared | §C.2 | none |
| `genP`, `entry₀`, `genData₀`, `GenData`, `CallEdge`, `ordCallees`, `TopShips`, `Pkg` field access | owner names and argument orders; `GenPInv` deleted | §C.5 | `GenData`, `genSem`, `ordCallees`, `genData₀` are `AssignKit` fields with no Lean of their own yet |
| `ConstValue` / `CV` | definable part / table part separated | §C.6 | the table (Q4): decision document, not adopted |
| connection of abstract `Match/Obs/shapeOf` | complete instance; needs `Pk : Type u` in Part A | §C.2 | U-UNIV |

## C.1 Source facts used, and how they were checked

Re-read at this tree (base 08e97dba = par/gen3-combined 9d26005c + DC files) unless a branch is named. `file:line`.

| fact | where |
|---|---|
| binder kinds `.domain` for `DomainConfig`, `.bool` for `Signal _ Bool`, `.bits n` for `Signal _ (BitVec n)` with `n` a canonical positive literal; **the domain argument of `Signal` is ignored** | `Sparkle/Compiler/Elab.lean:2337` (`mixedGateBinderKind?`), `:1389` (`canonicalNatLitValue?`) |
| `telescopeKinds` maps a Pi-telescope to kinds, `none` on a non-hardware binder | `Elab.lean:4367` |
| result ports: `Prod a b` of two Signal kinds ↦ `out_0`, `out_1` (ctor `Prod.mk`); one Bool/BitVec Signal ↦ `out`; a user structure ↦ one port per field; `Signal _ (A × B …)` ↦ ONE port `out` (`machTupleKinds?`) | `Elab.lean:3859` (`machOuts?`), `:3835` (`machTupleKinds?`), `:5072-5085` (`machineShape?` chooses between them) |
| output fields: name, `lo`, `width`, `ty`; for kind `k`: `ty = machHWType k` (`.bit` for `.bool`, `.bitVector n` for `.bits n`), `width = machWidth k` (1 / n), in the order of the port list | `Elab.lean:4457` (`machHWType`), `:4463` (`machOutFields`), `:4313` (`machWidth`), `Sparkle/IR/Machine.lean:40` (`OutField`) |
| a tuple-typed INPUT is packed into one port (`packTupleInputs`); so a declaration with a `Prod` input has binders in the machine shape that are not those of its type | `Elab.lean:5077` |
| source observation `Pkg.src p : ∀ i, (Nat → Signal (dom i) Bool) → (Nat → (n : Nat) → Signal (dom i) (BitVec n)) → List (Nat → Nat)` | `Tools/ShippingGen2Pkg.lean:55` |
| input streams are indexed by the binder's telescope POSITION (domain binders counted): `boolsOf`/`decB` use `portIdx bs p` = number of non-domain binders before `p`; the quotation uses `bools (bpos j)` | `Tools/ShippingMachineSeqChild.lean:24,29`, `Tools/ShippingMachineChild.lean:49,53`, `Tools/ShippingMixedSourceBridge.lean:63,151,159-172` |
| a Bool is observed as `0/1` (`encodeBool`), a BitVec as `toNat` | `Tools/ShippingMuxLoweringSoundness.lean:16`, `Tools/ShippingMachineDenote.lean:40` (`enc`) |
| `MachineData.bsIn = shape.binders.take nIn`; `kDOf d = d.nIn - d.shape.insts.length` | `Tools/ShippingMachineAuto.lean:172-215`, `kjob/g5sm-u3:Tools/ShippingGen5SemGen.lean` (`kDOf`) |
| `Signal` is a structure with field `val : Stream α`, `Stream α = Nat → α`; `Signal.atTime s t = s.val t` | `Sparkle/Core/Signal.lean:83,92,105` (rev3 wrote `atTime`; `val` is used below) |
| `Pkg ι dom : Type 1` (it holds `Type`-valued fields) | observed: the scratch elaboration of `DCGen … (Pk := Pkg ι dom)` fails with `Pk : Type` and succeeds with `Pk : Type u` |
| `Pkg.ok`, `Pkg.body_eq` are THEOREMS by cases for every `Pkg`; there is no `Pkg.init` | `Tools/ShippingGen2Pkg.lean:88,94` |

**How the Lean texts below were checked (rev4).** (i) Every signature was copied from the file:line named. (ii) Every Lean block in §C.2, §C.3 was put in a scratch file
(local, in the session scratchpad, NOT committed, NOT evidence) and elaborated with `kjob lake env lean <scratch>` against the oleans of this tree, with
`set_option autoImplicit false`: §C.2 elaborates; the instance equation `DeclConnect … = (∀ X, …)` closes by `rfl`; the `sigShape?` function was run on seven
test declarations (`tA`: two scalar args, Bool result ↦ `some`; `tB`: a `Prod` result ↦ `some`; a second domain binder, a `{α : Type}` binder, a closed `defaultDomain`,
a three-way `Prod` result, and a zero-width `BitVec` result ↦ `none`); `FG_COMPLETE` elaborates with a local copy of `envAt` (`Tools/ShippingEntryReadsLinked.lean:249` could not be imported because that
module was not built in the scratch cache; the body was copied). (iii) The three agreement lemmas (§C.2) elaborate as statements; the proof of `outPorts_eq` was
found in scratch (`cases` + `simp`), the proofs of the other two are the unit's work. (iv) What is NOT checked: `DataSoundAt` (the module `Tools.ShippingGen5DataOfPure` is on another branch
and was not imported), anything about `AssignKit`/`genP` (DG-ACC has no Lean), `ShapeMatches` against a real `MachineData` of a corpus declaration.
The final check is a TYPE comparison in `Tests/Gen5/DeclConnectCheck.lean` (§C.8), not this scratch run.

## C.2 Concrete types (complete)

Namespace `Tools.ShippingGen5DeclConnect`, `set_option autoImplicit false`. Imports: `Tools.ShippingGen2Defs` (`Pkgs`, `Pkg`), `Tools.ShippingGen5DeclConnectAbs`
(Part A, after U-UNIV). Opens `Lean Sparkle.Compiler.Elab Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Tools.ShippingGen2 Tools.ShippingMachineAuto`
and `Tools.ShippingMuxLoweringSoundness (encodeBool)`. `variable {ι : Type} {dom : ι → DomainConfig}`.

No `MixedGateBinder.domain` appears among the arguments or results of a shape: a separate `Scalar` kind removes the "unreachable `.domain`" cases of rev3.

```lean
inductive Scalar
  | bool
  | bits (n : Nat)
  deriving DecidableEq, Repr

def Scalar.Ty (D : DomainConfig) : Scalar → Type
  | .bool => Signal D Bool
  | .bits n => Signal D (BitVec n)
def Scalar.binder : Scalar → MixedGateBinder
  | .bool => .bool
  | .bits n => .bits n
def Scalar.hw : Scalar → Sparkle.IR.Type.HWType
  | .bool => .bit
  | .bits n => .bitVector n
def Scalar.width : Scalar → Nat
  | .bool => 1
  | .bits n => n
/-- The actual function's argument at telescope position `q`: `bools q` / `bits q n` (`decB`/`decV` indexing, §C.1). -/
def Scalar.arg {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n))
    (q : Nat) : (k : Scalar) → k.Ty D
  | .bool => bools q
  | .bits n => bits q n
/-- Observation of one result stream: Bool as 0/1, BitVec as `toNat`. -/
def Scalar.obs {D : DomainConfig} : (k : Scalar) → k.Ty D → (Nat → Nat)
  | .bool, s => fun t => encodeBool (s.val t)
  | .bits _, s => fun t => (s.val t).toNat

inductive ResShape
  | one (k : Scalar)
  | pair (ka kb : Scalar)
  deriving DecidableEq, Repr

def ResShape.Ty (D : DomainConfig) : ResShape → Type
  | .one k => k.Ty D
  | .pair a b => a.Ty D × b.Ty D
def ResShape.obs {D : DomainConfig} : (r : ResShape) → r.Ty D → List (Nat → Nat)
  | .one k, s => [k.obs s]
  | .pair a b, (x, y) => [a.obs x, b.obs y]
/-- The output ports a package must have, in `layout.outs` order: name, hardware type, width (`machOuts?` + `machOutFields`). -/
def ResShape.outPorts : ResShape → List (String × Sparkle.IR.Type.HWType × Nat)
  | .one k => [("out", k.hw, k.width)]
  | .pair a b => [("out_0", a.hw, a.width), ("out_1", b.hw, b.width)]
/-- The same ports as `machOuts?` returns them, for the agreement lemma. -/
def ResShape.ports : ResShape → List (String × MixedGateBinder)
  | .one k => [("out", k.binder)]
  | .pair a b => [("out_0", a.binder), ("out_1", b.binder)]
def ResShape.ctor? : ResShape → Option Name
  | .one _ => none
  | .pair _ _ => some ``Prod.mk

/-- Shape of the actual type: the arguments AFTER the leading `DomainConfig` binder, and the result. -/
structure SigShape where
  args : List Scalar
  res : ResShape
  deriving DecidableEq, Repr

def ArgsTy (D : DomainConfig) : List Scalar → Type → Type
  | [], R => R
  | k :: ks, R => k.Ty D → ArgsTy D ks R
/-- The reference type: a function of the domain. -/
def SigShape.Ty (sh : SigShape) : Type := (D : DomainConfig) → ArgsTy D sh.args (sh.res.Ty D)

/-- Feed the reference streams: argument `k` at position `q` gets `k.arg bools bits q`; the domain binder is position 0, so the first call has `q = 1`. -/
def applyArgs {D : DomainConfig} (bools : Nat → Signal D Bool) (bits : (j : Nat) → (n : Nat) → Signal D (BitVec n)) :
    (ks : List Scalar) → (q : Nat) → (R : Type) → ArgsTy D ks R → R
  | [], _, _, f => f
  | k :: ks, q, R, f => applyArgs bools bits ks (q + 1) R (f (k.arg bools bits q))

def SigShape.obs (sh : SigShape) (v : sh.Ty) (i : ι) (bools : Nat → Signal (dom i) Bool)
    (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n)) : List (Nat → Nat) :=
  sh.res.obs (applyArgs bools bits sh.args 1 (sh.res.Ty (dom i)) (v (dom i)))
```
`SigShape.obs` has `dom` implicit and is called `sh.obs (dom := dom) v i bools bits` (it is determined by `i`'s type only through `dom i`, so it cannot be inferred from the arguments).

`sigShape?` — a total function of the type `Expr` ALONE. `depth` = number of binders already opened; a domain argument at `depth` must be the loose bound variable of the
FIRST binder, i.e. `.bvar (depth - 1)`:

```lean
def domAt (depth : Nat) : Lean.Expr → Bool
  | .bvar j => j + 1 == depth
  | _ => false
def scalar? (depth : Nat) : Lean.Expr → Option Scalar
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) d) (.const ``Bool _) =>
    if domAt depth d then some .bool else none
  | .app (.app (.const ``Sparkle.Core.Signal.Signal _) d) (.app (.const ``BitVec _) wE) =>
    if domAt depth d then (canonicalNatLitValue? wE).bind fun n => if 0 < n then some (.bits n) else none else none
  | _ => none
def resShape? (depth : Nat) : Lean.Expr → Option ResShape
  | .app (.app (.const ``Prod _) a) b => do
    let ka ← scalar? depth a
    let kb ← scalar? depth b
    pure (.pair ka kb)
  | e => (scalar? depth e).map .one
def sigGo : Nat → List Scalar → Lean.Expr → Option SigShape
  | depth, acc, .forallE _ ty b _ => (scalar? depth ty).bind fun k => sigGo (depth + 1) (acc ++ [k]) b
  | depth, acc, e => (resShape? depth e).map fun r => { args := acc, res := r }
def sigShape? : Lean.Expr → Option SigShape
  | .forallE _ ty b _ => if ty.isConstOf ``Sparkle.Core.Domain.DomainConfig then sigGo 1 [] b else none
  | _ => none
/-- The decision on a declaration: `levelParams` is a property of the constant, not of its type. -/
def shapeOf (ci : ConstantInfo) : Option SigShape := if ci.levelParams.isEmpty then sigShape? ci.type else none
```
Everything outside this fragment is `none` (never `PUnit`, never a weaker meaning): a second domain binder, a closed or different domain term, a non-`Signal` binder, an
implicit `Type` binder, a user-structure result, a packed-tuple result (`Signal D (A × B)`), a three-way `Prod`, a zero-width `BitVec`, a non-literal width.
Because `sigShape?` is stricter than `telescopeKinds`/`machOuts?` (it checks the domain argument they ignore), the three agreement lemmas of units U-SHAPE2 hold in the direction needed:

```lean
theorem sigShape?_telescope {ty : Lean.Expr} {sh : SigShape} (h : sigShape? ty = some sh) :
    telescopeKinds ty = some (MixedGateBinder.domain :: sh.args.map Scalar.binder)
theorem sigShape?_machOuts (senv : StructEnv) {ty : Lean.Expr} {sh : SigShape} (h : sigShape? ty = some sh) :
    machOuts? senv ty = some (sh.res.ctor?, sh.res.ports)
theorem outPorts_eq (r : ResShape) (slotsW : Nat) :
    r.outPorts = (machOutFields slotsW r.ports).map (fun o => (o.name, o.ty, o.width))
```

What the shape must match in the package (ties the adapter to THIS package; arguments and results are kept by construction, state is not the adapter's job):

```lean
def ShapeMatches (sh : SigShape) (d : MachineData) (kD : Nat) : Prop :=
  (d.bsIn.take kD).map (·.2) = MixedGateBinder.domain :: sh.args.map Scalar.binder ∧
  d.shape.layout.outs.map (fun o => (o.name, o.ty, o.width)) = sh.res.outPorts
```
Input correspondence is therefore positional and exact: the declaration's `q`-th argument is `bools q` / `bits q n`, the domain is `dom i`. Output correspondence: `sh.obs`
lists the results in port order; `ShapeMatches` makes that list as long as `layout.outs` and equal in type/width. State: the actual machine's state is internal
(`runCircuitH`/`Signal.loop`), not an argument or a result; it is the content of the `CV`-and-`Obs` equation (rows 3/4 of §C.7), not of the adapter.

The instance of the abstract core (after U-UNIV, Part A with `{Pk : Type u}`):

```lean
abbrev ConstValueRel := Environment → Name → (α : Type) → α → Prop
def MatchC (sh : SigShape) (p : Pkg ι dom) : Prop := ShapeMatches sh p.d p.kD
def ObsC (p : Pkg ι dom) (sh : SigShape) (v : sh.Ty) : Prop :=
  ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits
def DeclConnect (CV : ConstValueRel) (env₀ : Environment) (P : Pkgs ι dom) (Tgt : Name → Prop) : Prop :=
  Tools.ShippingGen5DeclConnectAbs.DCGen (fun e n => e.find? n) CV shapeOf (fun sh p => MatchC sh p) (fun p sh v => ObsC p sh v) P env₀ Tgt
-- checked in scratch by `rfl`:
example (CV env₀ P Tgt) : DeclConnect CV env₀ P Tgt = (∀ X, Tgt X → ∀ p, P X = some p →
    ∃ (ci : ConstantInfo) (sh : SigShape) (v : sh.Ty), env₀.find? X = some ci ∧ shapeOf ci = some sh ∧ ShapeMatches sh p.d p.kD ∧
      CV env₀ X sh.Ty v ∧ ∀ i bools bits, sh.obs (dom := dom) v i bools bits = p.src i bools bits) := rfl
```
The abstract parameters map as `E := Environment`, `N := Name`, `CI := ConstantInfo`, `Pk := Pkg ι dom`, `Shape := SigShape`, `Ty := SigShape.Ty`, `find := Environment.find?`,
`Match := MatchC`, `Obs := ObsC`. **Universe finding:** `Pkg ι dom : Type 1`, but Part A's `variable {E N CI Pk : Type}` forces `Pk : Type`. U-UNIV changes that `variable` line to
`{E N CI : Type} {Pk : Type u}` (the file already has `universe u`). A scratch copy with this change elaborates without any other edit (all of `Tools/ShippingGen5DeclConnectAbs.lean`).
This edits an accepted file; its rebuild and a re-run of the Part A audit are part of U-UNIV (§C.8). Nothing else in Part A changes.

`CV env₀ X sh.Ty v` must carry that `ci.type` denotes `sh.Ty` (rule T of §C.6), otherwise a `v : sh.Ty` unrelated to `X`'s declared type could be offered.
`DeclConnectImp` (the implication form, INTERMEDIATE, true for the empty relation) is `DCImp` of Part A and is not used for completion.

## C.3 `FG_COND` (conditional schema) and `FG_CONNECT` (final connection obligation); binders complete, owner-premises explicit

FG (GENERAL_SPEC.md:88-93, the schema, not edited):
`FG : ∀ (L : Laws mref cref) declName (parameters : List (String × Nat)) mctx cctx w b D w', Start L mctx cctx w → (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨ RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') → ReflectsAll L declName parameters → ∃ p n, Pk declName = some p ∧ TopShips p n declName b raw D`.

Binder sources (copied, then elaborated, §C.1):

| FG name | Lean type | source |
|---|---|---|
| `mref`, `cref` | `ST.Ref IO.RealWorld Meta.State`, `ST.Ref IO.RealWorld Core.State` | `Tools/ShippingGen2Defs.lean:46` (`Laws`) |
| `L` | `Laws mref cref` | `Tools/ShippingGen2Defs.lean:46` |
| `declName` | `Name` | `Sparkle/Compiler/Elab.lean:8920` (`synthesizeCombinational (declName : Name)`) |
| `parameters` | `List (String × Nat)` | `Elab.lean:8940` |
| `mctx`, `cctx` | `Meta.Context`, `Core.Context` | `Tools/ShippingGen2Defs.lean:52` (`Start`) |
| `w`, `w'` | `Void IO.RealWorld` | `Tools/ShippingEntrySoundness.lean:937` (`RunsTo`) |
| `b` | `Sparkle.IR.AST.Module` (first component of the entry's result) | `Elab.lean:8920,8940`: `MetaM (Sparkle.IR.AST.Module × Sparkle.IR.AST.Design)` |
| `D` | `Sparkle.IR.AST.Design` (second component) | same |
| `Start L mctx cctx w` | `Prop` | `Tools/ShippingGen2Defs.lean:52` |
| `RunsTo m mctx mref cctx cref w a w'` | argument order exactly this | `Tools/ShippingEntrySoundness.lean:937` |
| `TopShips p n declName b raw D` | `p : Pkg ι dom`, `n : Nat`, `declName : Name`, `b raw : Module`, `D : Design` | base: `Tools/ShippingGen2Defs.lean:280`; S2 (`kjob/g2tc-s2` fa84af5d): `:282` |
| `envAt cref w` | `Environment` | `Tools/ShippingEntryReadsLinked.lean:249` |
| `ReadsAt env₀ cref w` (E1 `readsAt_self`) | `Prop`, 4 conjuncts | `Tools/ShippingGen5Env.lean:29,36` |

**Why two statements (R1).** rev4's `FG_COMPLETE` was FG's schema with `Pk := GP env₀`, plus two conjuncts. Read as a final guarantee it is satisfied vacuously in three ways:
(i) `Post b raw` is a hypothesis (`∀ raw, Post b raw → …`): with `Post := fun _ _ => False` the first conjunct holds for every run, and nothing says a `raw` exists;
(ii) with `GP := fun _ _ => none`, `DeclConnect` is `∀ X, Tgt X → ∀ p, P X = some p → …` over an empty hypothesis, hence true: it says nothing at `declName` (the package-existence content of rev3/rev4 sat only in the first
conjunct, which (i) already empties), and
(iii) `ConstValueFunctional CV` holds for the empty relation (and for any relation with at most one value per name), so it carries no content without a separate non-emptiness fact.
Hence `Post = False`, `GP = none`, `CV = empty` satisfy all three conjuncts at a run that does exist, in particular when the run has succeeded and the compiler produced `(b, D)`.
A statement that is a true final guarantee must not be satisfiable by `Post = False`, `GP = fun _ _ => none` or `CV = fun _ _ _ _ => False` at a run that exists.
rev5 therefore fixes two statements and says which is which:
- `FG_COND` — the rev4 text, renamed: the **conditional schema**. It is FG with the package assignment as a parameter, plus V2 and `DeclConnect` as stated conjuncts. It is NOT reported as a final guarantee.
- `FG_CONNECT` — `FG_COND` plus the **connection obligation for the same witness**: for every entry run witness `(declName, parameters, mctx, cctx, w, w', b, D)` that satisfies `Start`, the route disjunct and `ReflectsAll`,
  (O1) `∃ raw, Post b raw` (the post-processing relation holds for this very `(b, D)`), (O2) `∃ p, GP (envAt cref w) declName = some p`, and (O3) the FG conclusion for every `raw` with `Post b raw`.
  The conjunct `DeclConnect` is then taken at that same package assignment and the target `TgtRun`, whose `top` constructor contains `declName`, so `DeclConnect` has a package to be about at `declName`.
M4 has not fixed `Post` or `ReflectsAll` in Lean (below). Until it does, `FG_CONNECT` is a statement PARAMETRIZED by two relations whose satisfiability on the actual entry is exactly (O1) and the premises of FG; it is an INTERMEDIATE,
not a "complete" form, and the name `FG_COMPLETE` is withheld until `Post`/`ReflectsAll` are definitions and the instantiation is proved.

**TopShips: S2 vs base (R3).** `kjob/g2tc-s2` fa84af5d (R-G; the brief records it as scoped accepted) changes only the BODY of `TopShips`: the premises `∀ t, ins t "rst" = 0` and `∀ t st, seedIn b ins t st "clk" = 0`
become `"rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0` and `"clk" ∈ b.inputs.map (·.name) → ∀ t, ins t "clk" = 0` (diffed against the base text). Its signature `(p n declName b raw D)` is unchanged.
**Direction (corrects rev4, which wrote "weaker"):** `TopShips` is a conclusion that holds under input premises. Under R-G the premises are *weaker* (required only when the module has the input), so the conclusion is claimed for MORE executions:
for a module without a `clk`/`rst` input it now covers all inputs streams instead of only those with `clk = 0`/`rst = 0` it never reads; for a module with both inputs it is the old contract. R-G is therefore a STRENGTHENING of the
no-clock guarantee (TOP_CONTRACT_REVISION.md §2 R-G), which is S2's guarantee question — recorded here, not decided here.
`FG_COND`/`FG_CONNECT` mention `TopShips` only as a constant and do not unfold it, so their text is identical under both versions; their MEANING differs. Consequences for the check (§C.8):
- an `inferType` comparison of `TopShips` (signature) is satisfied by the base AND the S2 text, so it does NOT detect a change of the contract body. rev5 does not rely on it for that purpose;
- while `TopShips` in this tree is the base version, `FG_CONNECT`'s meaning depends on S2: the dependency is stated explicitly and not hidden. Choice made here: **(a)** an explicit dependence on the existing R-G audit
  (`Tests/Gen2/TopNCCheck.lean` and its re-pinned `TopShips` checks at `kjob/g2tc-s2` fa84af5d, commit 21342039 "Defs TopShips switched to R-G"): `FG_CONNECT` is reported "relative to the R-G contract as audited there",
  and the final theorem's closure list names `TopShips` as an owner constant of S2; **(b)** once S2 is merged, `DeclConnectCheck` adds a BODY pin: `TopShips`' `defnInfo` value is compared (same comparator as the other definitions) with an independently written
  expected body, plus one-change mutants (the `rst` premise restored unconditionally; the `clk` premise restored unconditionally). (b) cannot be written against this tree (it would pin the base text, which S2 replaces); it is listed as a unit, not done.
Any check that pins the text of `Tools/ShippingGen2Defs.lean` must be re-pinned when S2 merges; this unit adds none now.

**Owner-premises found by the binder audit (no Lean definition in this survey):**
- `ReflectsAll`: `git grep ReflectsAll` over `par/gen5-t2`, `par/gen3-induct`, `par/gen2-spec`, `kjob/g2tc-s2`, `kjob/g5do-r2`, `kjob/g5sm-u3`, `kjob/g5ac-309a33a9` and this tree finds it only in `.md` text (GENERAL_SPEC.md:92,98,483; DG_ENV_FREEZE.md:217,272). GENERAL_SPEC.md:98 says it is "fixed in M4". Parameter: `ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop`.
- `raw`: FG's text leaves `raw` free and says "(b, raw) related by the entry's post-processing" (:93, :100). The only Lean statements that bind `raw` take it from the CORE run and
  relate `b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)` (`T1Stmt`, `Tools/ShippingGen2Defs.lean:357-365`). For the ENTRY run `(b, D)` the relation is M4's deliverable. rev4/rev5 bind `raw` universally under a relation parameter `Post : Module → Module → Prop` (`∀ raw, Post b raw → …`), and rev5 adds the explicit existence obligation O1 `∃ raw, Post b raw`.
  Two other readings exist: `∃ raw` in the conclusion (adds an existence claim FG does not make) or a second `RunsTo (synthesizeCombinationalCore …)` premise (a different run). rev4 does not choose between a stronger `Post`; whichever M4 supplies must be satisfied by the actual entry, otherwise FG is shrunk. DeclConnect does not use `raw` at all (the two other conjuncts are independent of it).
- `Pk`: FG's `Pk` is a schema variable. FG-REF is `Pk := genP env₀`.

```lean
def ConstValueFunctional (CV : ConstValueRel) : Prop :=
  ∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w

inductive TgtRun (P : Pkgs ι dom) (declName : Name) : Name → Prop     -- least predicate: declName, and the callees of reached names whose instance origin has `child? = none` (this includes field instances; it is not only `origin = .ord`)
  | top : TgtRun P declName declName
  | call {c : Name} {q : Pkg ι dom} (hc : TgtRun P declName c) (hq : P c = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
      (ord : (q.d.shape.instOrigins.getD k .ord).child? = none) : TgtRun P declName (q.d.shape.insts[k]'hk).1

open Tools.ShippingEntrySoundness (RunsTo)
/-- The hypotheses of FG on one entry run (the witness): the start world, one of the two routes, `ReflectsAll`. Binders as in the table above. -/
def EntryWitness {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop) (L : Laws mref cref)
    (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design) : Prop :=
  Start L mctx cctx w ∧
  (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
   RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') ∧
  ReflectsAll L declName parameters

/-- CONDITIONAL SCHEMA (rev4's `FG_COMPLETE`, renamed). Not a final guarantee: vacuous at `Post = False`, `GP = none`, `CV = ∅` (see the text above). -/
def FG_COND {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : ConstValueRel) (L : Laws mref cref) : Prop :=
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧   -- FG with Pk := GP env₀ (FG-REF)
    ConstValueFunctional CV ∧                                                                                                   -- V2
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)

/-- FINAL CONNECTION (INTERMEDIATE while `Post`/`ReflectsAll` are parameters). For the SAME witness: a `raw` with `Post` exists (O1), a package exists (O2),
the FG conclusion holds for every such `raw` (O3), and `DeclConnect` is about that package assignment and the closure `TgtRun` of the entry (which contains `declName`). -/
def FG_CONNECT {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : ConstValueRel) (L : Laws mref cref) : Prop :=
  ConstValueFunctional CV ∧
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D →
    (∃ raw, Post b raw) ∧                                                                                                       -- O1
    (∃ p : Pkg ι dom, GP (envAt cref w) declName = some p) ∧                                                                    -- O2
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧   -- O3 (FG-REF)
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)
```
(`FG_COND` elaborated in scratch at rev4 with `envAt` copied locally; `EntryWitness` and `FG_CONNECT` are the same text with the binders factored and have NOT been elaborated; they are not in Lean.)

Non-vacuity facts the Lean unit must prove about `FG_CONNECT` (planned lemmas, statements only; each is a consequence of the definition, to be checked, not assumed):
- **NV-Post**: `FG_CONNECT ReflectsAll (fun _ _ => False) GP CV L → ¬ ∃ witness` (any witness gives `∃ raw, False`). So the carrier `Post` is not a way to weaken `FG_CONNECT`: the final instantiation must make the actual entry satisfy O1.
- **NV-GP**: `FG_CONNECT ReflectsAll Post (fun _ _ => none) CV L → ¬ ∃ witness` (O2 fails). Likewise `GP` cannot be trivialised.
- **NV-CV**: with `CV := fun _ _ _ _ => False`, `FG_CONNECT` and a witness with O2 give a contradiction (`not_declConnect_of_empty`, concrete form already in Lean, with `TgtRun.top`). So `CV` cannot be trivialised.
- **NV-witness**: UNSUPPLIED / execution evidence only. That an `EntryWitness` exists (a `Start` world, a `RunsTo` run of the entry, and `ReflectsAll` for it) is NOT shown by this unit. Successful corpus runs are execution evidence for the `Start`/`RunsTo` parts only; they do not give the logical existence of a triple `Start` + `RunsTo` + `ReflectsAll` (`ReflectsAll` has no Lean definition, and no run is supplied as a Lean term). The NV lemmas are therefore CONDITIONAL: they hold when an `EntryWitness` is given.
- **O2 is not logically independent**: O2 follows from O1 and O3 (O3 at a `raw` given by O1 yields the package). O2 is kept as an explicit stated obligation; a mutant that drops O2 is rejected only by the signature/defeq comparator and this is NOT evidence that O2 is logically independent of O1+O3.
Hence the final guarantee needs ALL of: `Post`/`ReflectsAll` as defined by M4 and satisfied by the actual entry (O1 and the premises of O3), `GP := genP …` (O2, supplied by DG-ACC/DG-SEM/DG-DATAOF/DC-COVER, unsupplied), `CV := ConstValueE …` (unsupplied, §C.6).

Instantiation at integration, none of which is a quantifier of the final theorem: `GP := fun env₀ => genP (K env₀) (hF env₀)` with DG-ACC's `genP` (§C.5); `CV := ConstValueE …` — the DCF unit's relation, so there is NO free `V3`
(rev3's `ConstValueOk CV V3` is withdrawn); `ReflectsAll`, `Post`: M4. `ConstValueFunctional (ConstValueE …)` is a PLANNED proof (§C.6): the relation's rules, the exclusivity/consistency condition between its
unfold and prim rules, and the induction are not written and are not claimed.

`env₀ := envAt cref w` is the START world's environment; `ReadsAt env₀ cref w` is E1 (`readsAt_self`). `parameters` appears twice, in the route disjunct and in `ReflectsAll`, as in FG. For a
parametric run `machineShape?` is `none` (`Elab.lean:5072-5075`: `symbolicMode || !parameters.isEmpty`), so `GP env₀ declName` may be `none`; FG's own conclusion then fails for that run unless `ReflectsAll`
excludes it, so (O2) is the same strength as FG there, not a weakening: the obligation is stated, not hidden.

`TgtRun` has the shape of `T1Hyp.closed`'s `Reach` (`Tools/ShippingGen2Defs.lean:218`); that `TgtRun ⊆ Reach` is G-REACH (unsupplied).

Not-shrunk checklist (properties the Lean unit must preserve; the check asserts them by `example`):

| FG property | preserved by | how it is checked |
|---|---|---|
| FG's quantifiers and hypotheses unchanged | binders of §C.3 are FG's list; no edit of `Tools/ShippingGen2Defs.lean` / `T1Hyp*` | `git diff` over the protected paths empty; binder-table TYPE check |
| all successful runs, both entries | `TgtRun` from the run's names, not a corpus list | no `Tgt` literal; `dcGen_mono` is the only way `Tgt` shrinks, as a lemma |
| no per-declaration premise | `DeclConnect`'s binders are `CV env₀ P Tgt`; `declConnect_of_rows` has only uniform rows | binder-table listing in the check |
| `DeclConnect` not vacuous | existence inside | U3 (Part A) |
| `GenWF` not strengthened, no new law | nothing here mentions them | grep in the check header |
| `ConstValueOk` not assumed | it is a conjunct, and `CV` is instantiated by a definition | statement text; CLOSURE of the final theorem |
| `Post` / `ReflectsAll` are not smuggled shrinkage | they are parameters of M4 | listed as owner-premises; the reviewer of M4 checks they are met by the actual entry |

## C.4 `DataSoundAt` (DG-DATAOF's `initOk`, real type)

DG-DATAOF rev1 (`git show kjob/g5do-r2:scripts/gen5/DG_DATAOF_FREEZE.md` §2.4, 8d20ae99) states `dataOf_sound`'s conclusion as
`d.shape = s ∧ d.ok = true ∧ d.shape.body = quote d.dom (fun j => inputExpr d.shape.binders.length (d.bpos j)) (fun j => inputExpr d.shape.binders.length (d.vpos j)) d.packed ∧ d.initOk (initsOf d) = true`,
where `initsOf : (d : MachineData) → HList (tys d.ss)` is `Tools/ShippingGen5DataOfPure.lean:354` (namespace `Tools.ShippingGen5DataOfPure`) and `MachineData.initOk (inits : HList (tys d.ss)) : Bool` is `Tools/ShippingMachineAuto.lean:248`.
The `GenFacts` fields `ok/body_eq/init` (`Tools/ShippingQuadComposed.lean:120-124`) have the same texts.

```lean
def DataSoundAt (p : Pkg ι dom) : Prop :=
  p.d.ok = true ∧
  p.d.shape.body = Tools.ShippingUnifiedSource.quote p.d.dom
    (fun j => inputExpr p.d.shape.binders.length (p.d.bpos j))
    (fun j => inputExpr p.d.shape.binders.length (p.d.vpos j)) p.d.packed ∧
  p.d.initOk (Tools.ShippingGen5DataOfPure.initsOf p.d) = true
```
Conjunct 1 and 2 are `Pkg.ok` and `Pkg.body_eq` (`Tools/ShippingGen2Pkg.lean:88,94`) for every `Pkg`. Conjunct 3 is not a theorem about an arbitrary `Pkg` (there is no `Pkg.init`, and a package's own `inits` need not be `initsOf p.d`);
it is DG-DATAOF's `dataOf_sound` for a package whose data is `dataOf`'s and whose `inits` is `initsOf`. `DataSoundAt` is NOT a hypothesis of any Part A unit and not of `FG_COMPLETE`;
it is the candidate content of `DataOk` (`T1Hyp.pkg`, `Tools/ShippingGen2Defs.lean:204`, a placeholder `Prop` parameter) at M5 integration. Not elaborated in rev4 (§C.1 (iv)).

## C.5 Dependencies: names and argument orders of the owners (nothing re-defined)

| name used here | owner | exact form | status |
|---|---|---|---|
| `GenWF (d : MachineData) : Bool`, `RowA/RowB/RowC`, `kDOf d = d.nIn - d.shape.insts.length` | DG-SEM U3 | `kjob/g5sm-u3` 309a33a9 `Tools/ShippingGen5SemGen.lean` (`namespace Tools.ShippingGen5Sem`) | built (agent build, header 4ebc4067) |
| `GenIn` (`d wf inits ok bodyEq init`), `genSemGenE X g eb ev : SrcSem ι dom` | DG-SEM U3 | same file | built |
| `SemPkg`, `FactsOf`, `Pkg.toSem`, `genPkg`, `semOf`, `toSem_genPkg` | DG-SEM | `Tools/ShippingGen5SemPkg.lean` | built (per DG-ACC freeze §1, g5smv-1cc605ef) |
| `AssignKit ι dom env₀` (fields `dataOf`, `GD`, `dOf`, `genData₀`, `ordCallees`, `genSem`, `mem_ordCallees`, `genData₀_dataOf`, `genSem_local`, `genSem_decl`, `genSem_d`) | DG-ACC | `kjob/g5ac-309a33a9:scripts/gen5/DG_ACC_FREEZE.md` §2 (`Tools.ShippingGen5Acc`) | freeze only |
| `entry₀ (env₀ : Environment) (X : Name) : Option ConstantInfo := (env₀.find? X).map fun ci => entryConst true false [] ci (instancePredicate env₀) (userInliner env₀) (structEnv env₀)` | DG-ACC | §3, explicit `env₀` FIRST | freeze only |
| `dataOf₀ K X`, `CallEdge K X c` (`K` explicit, ordinary instances only), `CallRel K := flip (CallEdge K)` | DG-ACC | §3 | freeze only |
| `genS K : Name → Option (SemPkg ι dom)`, `genS_some_inv`, `genS_unfold` | DG-ACC | §3.1 | freeze only |
| `GenSFacts K : Prop`, `genP K hF : Name → Option (Pkg ι dom)`, `GeneratedAtK K P X E p`, `genP_generated`, `genP_decl`, `genP_d_edges` | DG-ACC | §4 | freeze only |
| `GenData E senv`, `genSem Q X g`, `ordCallees d`, `genData₀ E` | DG-SEM / DG-DATAOF as `AssignKit` fields | `[M5]` `DGEN_FREEZE.md` §2.1; DG-ACC §2 table | no Lean of their own yet |
| `dataOf`, `initsOf`, `dataOf_sound` | DG-DATAOF | `kjob/g5do-r2` 8d20ae99 `Tools/ShippingGen5DataOfPure.lean` (`initsOf`, pure units), `Tools/ShippingGen5DataOf.lean` (`dataOf`: design only) | pure part: clean build dov-8d20ae99 was running when this was written; `dataOf`: freeze |

**`GenPInv` of rev3 is deleted.** It restated a conjunction that DG-ACC's `genS_some_inv` / `genP_generated` / `genP_d_edges` already prove (`∃ E g, entry₀ env₀ X = some E ∧ genData₀ E = some g ∧ Acc (CallRel K) X ∧ …`,
`p.d = d` with `dataOf₀ K X = some d`). DeclConnect's rows use those lemmas directly:
- `env₀.find? X = some ci` (conjunct 1 of `DCAt`) from `entry₀ env₀ X = some E`: pure, by `Option.map_eq_some_iff` on `entry₀`'s definition: `entry₀ env₀ X = some E → ∃ ci, env₀.find? X = some ci ∧ E = entryConst true false [] ci …` (unit U-ENTRY, §C.8, waits for the file that defines `entry₀`). It does not need `ReadsAt` (C0).
- `p.d = g.d` and `p.decl = X`: `genP_d_edges`, `genP_decl`; `kD`: `kDOf`.
- "the package of each ordinary callee exists" is `genS_isSome_of_cover` (DG-ACC §6), not restated.

## C.6 `ConstValue` (Q4, DCF study): what is a definition and what is a table

Goal: `CV := ConstValueE PT`, the least relation closed under the rules, so that `V3` is a definition and not a parameter (§C.3). The rules, with the classification the brief asks for.
`env` is an `Environment`; `e : Lean.Expr`; the denotation of a TYPE `τ` is a Lean `Type` (`TypeDenotes`), of a TERM `e : τ` a value of that type.

| rule | content | class | why |
|---|---|---|---|
| lit | `Expr.lit (.natVal n)` ↦ `n : Nat`; `(.strVal s)` ↦ `s : String` | **D (defined)** | by structure; no name involved |
| bvar | variable ↦ valuation entry | **D** | by structure |
| lam | `fun x : τ => b` ↦ the Lean function over the denotation of `b` in the extended valuation | **D** | by structure |
| app | `f a` ↦ application, with the type check `TypeDenotes` | **D** | by structure |
| let | `let x := v; b` ↦ the denotation of `b` with `x := ⟦v⟧` | **D** | by structure |
| const-unfold | `env.find? c = some (.defnInfo d)` with value `e` ↦ the denotation of `e` | **D** | the environment is the argument; the derivation is the inductive witness. NO termination claim: acyclicity of an arbitrary `Environment` is not available in the logic, so it is a derivation, not a recursion |
| typeDenotes (fragment) | `ci.type` ↦ `sh.Ty` for the `sigShape?` fragment | **D** | by `sigShape?` (§C.2): `Pi`/`DomainConfig`/`Signal D Bool`/`Signal D (BitVec n)`/`Prod` of those — but the denotations of the type formers `Signal`, `BitVec`, `Prod`, `Bool`, `DomainConfig` are a Name-to-Type correspondence, hence **T** for the formers; only the fragment's *shape* is D |
| const-prim | a constant with NO unfoldable value (constructor, recursor, quotient primitive, opaque, axiom, `implemented_by`/`extern`) or one deliberately not unfolded (`Signal.register`, `Signal.loop`, `runCircuitH`, `BitVec.*`, `Bool.*`, `Prod.mk/fst/snd`, `ite`, `Nat.add`, …) ↦ a named Lean term | **T (table)** | a row is a pair `Name ↦ Lean term`; "this `Name` datum is that Lean constant" is a fact about `Lean.Environment` data that Lean's kernel cannot check about the logic's own constants. Writing the table is a plain `def` (no axiom). Its correctness is the TRUSTED content |
| type-former prims | `Signal`, `BitVec`, `Prod`, `HList`, `Bool`, `Nat`, `DomainConfig`, the `Pi` ↦ `→` | **T** | same, for types |

Consequences (statements about this survey):
1. Everything that is not a `Name ↦ Lean term` pair is a definition: rules lit/bvar/lam/app/let/const-unfold and the shape of the typed fragment. Their "correctness" is only that the relation models the kernel's evaluation of these node kinds; it introduces no Name-keyed stipulation.
2. **Functionality is NOT derived from the table's uniqueness (R2).** rev4 wrote that `ConstValueFunctional (ConstValueE PT)` follows by induction when `PT` has one row per `Name`. That is not established. One row per `Name` says
   the prim rule gives one value for a name; it does not say that the prim rule and the const-unfold rule give the SAME value for a name that has both a `defnInfo` value and a table row (the table deliberately covers constants that
   are not unfolded, e.g. `Signal.register`, `BitVec.*`, which can be definitions), nor that the type-denotation relation `TypeDenotes` (used by `app`/`typeDenotes`) is itself functional. Two derivations for one `Name` with different values
   would refute functionality. What is needed, and is PLANNED (not written, not claimed):
   (a) the complete inductive rule list of `ConstValueE` (every rule with its premises and its `Dyn`/valuation typing), as the DCF unit's own freeze;
   (b) an exclusivity or consistency condition for const-unfold vs const-prim — either a side condition on const-unfold (`c ∉ PT.dom`, which makes the rules disjoint and the induction a case split) or a per-name consistency
       obligation (the prim's Lean term equals the denotation of the unfolded value), the latter being a fact about the table, not derivable from uniqueness;
   (c) determinism of lit/bvar/lam/app/let and of `TypeDenotes` under the valuation;
   (d) the functionality proof by induction on the two derivations, using (a)-(c).
   Until (a)-(d) exist, `ConstValueFunctional CV` is a conjunct of `FG_COND`/`FG_CONNECT` for an unspecified `CV`, not a theorem about `ConstValueE`.
3. The table is the place where the semantics is stipulated rather than derived. Whether that makes it a NEW TRUSTED boundary is NOT established: it depends on whether the rows can be written as ordinary definitions with their
   correctness derived (e.g. the minimal-table option of the decision document) or must be stated as unproved facts. Neither alternative is shown impossible, and no trusted boundary is adopted or required here. If a stated list of
   unproved rows turns out to be needed, GENERAL_SPEC.md:505-506 and the reporting rule would make it a USER decision; that point has not been reached. `scripts/gen5/DC_CONNECT_PRIM_TABLE_DECISION.md` (rev5) is written on this basis:
   background and options only, no decision requested now.
4. How small the table can be made is a survey item this survey did not run: how many distinct constants occur in the accepted `defnInfo` values of the corpus after maximal `const-unfold` is not measured. rev3's claim that "each prim entry corresponds to one reader node kind" is a hypothesis to check (TABLE-COVERAGE), not a result.
5. Not claimed: that `ConstValueE` is the true kernel semantics; that any table is complete; that the recursion is well-founded (it is an inductive family, so no termination claim is needed).

The inductive `ConstValueE` is NOT written in rev4 and its complete Lean (the `Dyn` universe design for terms-and-types, the valuation, the dependent `app`) is the DCF unit's own freeze. The rule design (rules, exclusivity/consistency between the unfold and prim rules, `TypeDenotes` determinism) and the minimal-table survey proceed now and do NOT wait on a decision; only what is proved is turned into Lean, and what is not proved is recorded as "unsupplied / no route found in this survey". A separate user decision is requested only if a stated, unproved list of rows (a new TRUSTED boundary) is concretely found to be needed; that is not requested now. What §C.2/§C.3 need from it is only the type `ConstValueRel` and `ConstValueFunctional`.

## C.7 Supplier table

Status columns: **Exists** = present in a Lean file; **Pure now** = a pure lemma this issue can write without any dependency; **Waits** = depends on an unfinished owner (SEM / DATAOF / ACC / COVER); **Unsupplied** = this survey found no source or route (not a claim of impossibility). `[S]` = in this tree (9d26005c base).

| need | supplier | status | notes |
|---|---|---|---|
| abstract `DCAt/DCGen/DCImp`, U1-U6 | `Tools/ShippingGen5DeclConnectAbs.lean` | **Exists** (approved, scoped) | `Pk : Type` must become `Type u` (U-UNIV) |
| `sigShape?` family, `Scalar`/`ResShape`/`SigShape`, `applyArgs`, `obs`, `outPorts`, `shapeOf`, `ShapeMatches` | §C.2 | **Pure now** | scratch-elaborated; no dependency |
| `sigShape?_telescope`, `sigShape?_machOuts`, `outPorts_eq` | structural induction on `Expr`; `cases` | **Pure now** | `outPorts_eq` proved in scratch |
| `applyArgs_nil/cons`, `SigShape.obs` unfolding | `rfl` | **Pure now** | |
| `DeclConnect := DCGen …` and its unfolding equation | §C.2 | **Pure now** (after U-UNIV) | `rfl` in scratch |
| `FG_COND`, `FG_CONNECT`, `EntryWitness`, `TgtRun`, `ConstValueFunctional` | §C.3 | **Pure now** as definitions (not yet in Lean; awaits §C.3 rev5 approval) | statement only; NV-Post/GP/CV are lemmas of the same unit; the proof is the whole issue |
| `env₀.find? X = some ci` | `entry₀`'s definition (DG-ACC §3) | **Waits** on the file that defines `entry₀` (A1) | pure once it exists; independent of C0 |
| `ci_of_readsAt`, `envR_of_readsAt` (E4/E5) | `Tools/ShippingGen5Env.lean:52,58` | **Exists** | evidence side only (`MachineDefines`), not DeclConnect's statement; needs C0 |
| `ReadsAt` at the run's worlds (C0) | DG-ENV | **Unsupplied** | DG_ENV_FREEZE §0 S1 |
| package exists, `p.d`, `p.decl`, `kD` | DG-ACC `genP`, `genP_generated`, `genP_decl`, `genP_d_edges`; DG-SEM `genSem_d/decl` | **Waits** (ACC freeze in review; SEM `genSem` no Lean) | |
| `Acc (CallRel K) X` | DG-ACC `acc_of_run` | **Waits**; `AccServedStmt`/`AccKeepChildStmt` have no producer | DG-ACC §10 |
| `DataSoundAt` | `Pkg.ok`/`Pkg.body_eq` [S]; `initOk_of_ok`, `dataOf_sound` DG-DATAOF | conj. 1-2 **Exists**; conj. 3 **Waits** | not used by U1-U6 or `FG_COMPLETE` |
| `GenWF`, coverage of `dataOf` on real runs | DG-COVER / WFCOVER | **Unsupplied** | |
| `sigShape? = some` on every successful target | DC-COVER | **Unsupplied** | if a corpus top is outside the fragment: extend `ResShape` with its meaning (struct, packed tuple, tuple input), never weaken the statement |
| row 0: `∃ α v, CV env₀ X α v` | `ConstValueE` (DCF) | **Unsupplied** | rule design and minimal-table survey proceed (no decision awaited); a new TRUSTED boundary only if concretely found necessary |
| row 1: unfolding `ci.value ↦ entryConst …` preserves `CV` | `entryConst` (`Elab.lean:5272`) is definition unfolding; `EntryDefines` (`ShippingInlineSoundness.lean:48-57`), `entry_kept` (`ShippingEntrySoundness.lean:1132`) relate Exprs and RUNS | **Unsupplied** (depends on `CV`) | |
| row 2 shape/body | `dataOf_sound` + `readTerm_sound` (`ShippingReaderTerm.lean:1129`), `readN_expr_sound` (`ShippingReaderApp.lean:356`) | **Waits** on DG-DATAOF / READKINDS | |
| row 3 quote/eval agreement per node kind | `ConstValueE`'s rows vs the reader's table | **Unsupplied** | one row per node kind |
| row 4 `src = obsR (stateLoop …)` | `X.machine_source` per declaration (`ShippingMachineCommand.lean:2599-2610`); `GenFacts.source` for a package | per declaration **Exists**; uniform **Unsupplied** | |
| row 5 calls | `Acc` induction (Part A U5/U6) and E1 at the `ext` position (T2COVER §1) | skeleton **Exists**; per-call step = rows 3+4 at the callee | memory entries: DC-SUPPLY |
| `Tgt X ⇒ P X = some p` | DG-PKGASSIGN (`genP_pkg`, DG-ACC §6) | **Waits** | |
| `Post`, `ReflectsAll` (and O1: `∃ raw, Post b raw` on the actual entry) | M4 | **Unsupplied** | §C.3; until supplied `FG_CONNECT` is an intermediate parametrized statement |
| TopShips (R-G) | `kjob/g2tc-s2` fa84af5d (`Tests/Gen2/TopNCCheck.lean`, brief: scoped accepted) | not merged into this tree | not unfolded by DC; `FG_CONNECT` is relative to the R-G contract as audited there (§C.3 R3); body pin after merge |

## C.8 Units for the Part C implementation, and the audit plan

Order, each unit in a NEW file or the named edit, built one target at a time in the Pod, SHA recorded by a comment-only commit; per the issue rules the Lean commit stays `doing` with "clean build is the coder's".

| unit | content | needs | state |
|---|---|---|---|
| **U-UNIV** | `Tools/ShippingGen5DeclConnectAbs.lean`: `variable {E N CI : Type} {Pk : Type u} {Shape : Type} {Ty : Shape → Type}`; re-run of `Tests.Gen5.DeclConnectAbsCheck` (TYPE/MUTANT/AXIOMS/CLOSURE) plus a universe check (the seven `Pk`-carrying statements are universe-polymorphic; `Pk := Type` instantiates) | Part A | **implemented** cef857c6 (agent build exit 0; clean build is the coder's); edit of an accepted file, proofs unchanged |
| **U-SHAPE1** | `Tools/ShippingGen5DeclConnect.lean`: `Scalar`, `ResShape`, `SigShape`, `ArgsTy`, `applyArgs`, `SigShape.obs`, `outPorts/ports/ctor?`, `domAt/scalar?/resShape?/sigGo/sigShape?`, `shapeOf`, `ShapeMatches` (+ `Decidable`), `MatchC`, `ObsC`, `DeclConnectAt`, `DeclConnect`, `ConstValueRel` | U-UNIV, `Tools.ShippingGen2Defs` | **implemented** 68f1be34 (agent build exit 0). NOT in this file: `ConstValueFunctional`, `TgtRun`, `EntryWitness`, `FG_COND`, `FG_CONNECT` (§C.3 rev5 awaits approval) |
| **U-SHAPE2** | `sigShape?_telescope`, `sigShape?_machOuts`, `outPorts_eq`, `applyArgs_nil/cons`, helpers `scalar?_kind`, `scalar?_outs`, `resShape?_outs`, `sigGo_tele`, `sigGo_outs`, `declConnect_eq` (`rfl`), `declConnect_mono`, `not_declConnect_of_empty` | U-SHAPE1 | **implemented** 68f1be34; no `sorry`; axioms ⊆ {propext, Classical.choice, Quot.sound} |
| **U-ENTRY** | `entry₀_find`: `entry₀ env₀ X = some E → ∃ ci, env₀.find? X = some ci ∧ E = entryConst …` | DG-ACC A1 (the file defining `entry₀`) | waits |
| **U-ROWS** (conditional) | `declConnect_of_rows`: `dcGen_of_rows` at the concrete `DeclConnect` with `hstep` as an explicit hypothesis; INTERMEDIATE Acc assembly, supplies none of the rows | U-SHAPE1 | **implemented** 68f1be34 (the step is NOT proved; no row is supplied) |
| U-FG | `ConstValueFunctional`, `TgtRun`, `EntryWitness`, `FG_COND`, `FG_CONNECT` and the conditional non-vacuity lemmas NV-Post/NV-GP/NV-CV | §C.3 rev5 (scoped approved) | **implemented** (agent g5dc-r6, agent build exit 0, clean build is the coder's): `Tools/ShippingGen5FG.lean` (defs, `nv_post`/`nv_gp`/`nv_cv`, `o2_of_o1_o3`, `fgCond_trivial`) and `Tests/Gen5/FGCheck.lean` (by category: TYPE 9 theorem/definition level, constructors NOT included; CTOR TYPE 2 = `TgtRun.top`/`call` against independently written complete telescopes (names, order, binder infos, types at reducible transparency); MUTANT 11 theorem level + CTOR MUTANT 6 (ord 2, parent reach 2, pkg correspondence 1, `top` 1); AXIOMS 12; all signature/defeq rejections, not semantic counterexamples; the earlier "MUTANT 12" was a miscount; value closure of `FG_CONNECT`/`FG_COND` with required owner constants + controls). NV lemmas are conditional on an `EntryWitness`. Still OPEN: supply of Post/ReflectsAll from a real run and scope preservation, parametric/defaultDomain/struct coverage, DCF (`ConstValueFunctional` stays planned; rule design and minimal-table survey not yet run in this pass: no route found yet, not a claim of impossibility), FG completion |
| DCF | `ConstValueE` (rules, exclusivity/consistency, functionality: §C.6 (a)-(d)) | its own freeze | planned |
| final connection | `FG_CONNECT (…) L` at `GP := genP …`, `CV := ConstValueE …`, M4's `Post`/`ReflectsAll` | DG-SEM/DATAOF/ACC/COVER, DCF, M4 | not before |

**Aggregate (DeclConnectCheck + FGCheck, clean build dc7v-6bd33fd7 exit 0, 748 jobs, scoped approved at 6bd33fd7):** TYPE 23 (14 + 9) + CTOR TYPE 2; signature/defeq MUTANT 25 (14 + 11) + CTOR MUTANT 6; recognizer-copy mutants 2 are a separate class (finite-battery disagreement, not signature rejection). None is a semantic counterexample. Core-module/opaque exploration boundaries remain; FG_COND/FG_CONNECT are conditional, not FG completion.

Audit of `Tests/Gen5/DeclConnectCheck.lean` (implemented at 68f1be34; agent build exit 0; the clean issue-linked build is the coder's). Same discipline as Part A §4.1; every "mutant" is a signature/defeq (or finite-battery) rejection, NOT a semantic counterexample.
- **TYPE** (independent `Exp*`, compared by `Tests.Gen3.ExpectedType.checkExpected`: binder names, binder infos, types, then the conclusion; a non-syntactic match is logged as `GEN3 DEFEQ`): 14 targets — `declConnect_eq`, `declConnect_mono`, `not_declConnect_of_empty`,
  `declConnect_of_rows`, `sigShape?_telescope`, `sigShape?_machOuts`, `outPorts_eq`, `applyArgs_cons`, `applyArgs_nil` (theorems) and the VALUES of `ShapeMatches`, `SigShape.obs`, `shapeOf`, `DeclConnect`, `ObsC` (non-recursive definitions).
  Layering: `declConnect_eq` pins the unfolded `∀ … ∃ …` text; the value of `DeclConnect` is pinned as the `DCGen` instance; the theorems about `DeclConnect` use it as a constant. Not pinned by value: the recursive `sigShape?` family (behaviour battery instead).
- **MUTANT** (well-typed, one change, rejected by the same comparator): 14 signature/defeq rejections (+ 2 recognizer-copy mutants under BEHAVIOUR, rejected only by disagreement on the finite battery, so 16 in total) — `declConnect_eq` without the `ShapeMatches` conjunct; `mono` with the inclusion reversed; `not_declConnect_of_empty` without `¬`; `rows` without `hAcc`; `telescope` without the leading domain kind;
  `machOuts` with the constructor forced to `none`; `outPorts_eq` with `slotsW + 1`; `applyArgs_cons` without `q + 1`; `ShapeMatches` without `.domain ::` and without the output conjunct; `SigShape.obs` starting at position 0; `shapeOf` ignoring `levelParams`;
  `DeclConnect` as `DCImp` (the implication form); `ObsC` observing the package against itself. `applyArgs_nil` has NO mutant: `applyArgs … [] (q + 1) R f = f` is defeq to the statement, so a defeq comparator cannot reject a position change there.
  The Bool-observation mutant of rev4 (an identity on a `Bool` result against a `Nat` result) was ill-typed and is dropped; the observation `Scalar.obs` is covered by the axioms/closure checks and by `SigShape.obs`'s value pin, not by an ill-typed variant. (A well-typed Bool change, e.g. `if s.val t then 0 else 1`, is a candidate for a later behavioural check; it is not claimed here.)
- **AXIOMS**: `checkAxioms` on 26 constants (the 9 theorems above, the 5 helper lemmas, `sigShape?`, `shapeOf`, `ShapeMatches`, `SigShape.obs`, `DeclConnect`, `DeclConnectAt`, `MatchC`, `ObsC`, `Scalar.obs`, `ResShape.obs`, `ResShape.outPorts`, `applyArgs`): standard axioms only, no `sorryAx`.
- **BEHAVIOUR, battery** (11 local declarations with independently written expected `Option SigShape` and expected `shapeOf`): `tA` (Bool, BitVec 8 → Bool) and `tB` (Bool → `Signal Bool × Signal (BitVec 4)`) accepted; `tC` second domain binder, `tD` closed `defaultDomain`, `tE` implicit `Type` binder,
  `tF` three-way `Prod`, `tG` zero-width result, `tH` packed tuple `Signal D (BitVec 4 × BitVec 4)`, `tI` argument in a closed domain with an open result domain, `tJ` non-literal width: `none`; `tK` (explicit universe parameter that the type does not mention): `sigShape? = some`, `shapeOf = none`.
  Two one-change copies of the recognizer (domain term not checked; zero width allowed) must differ from `sigShape?` on the battery: they do, on `tI` and on `tG` respectively (finite battery, not an equivalence proof). Where the type is accepted, `telescopeKinds` agrees with the expected kinds and `machOuts?` returns `some`.
- **BEHAVIOUR, corpus controls** (chosen by the coder, as the brief allows; real declarations of the machine-route tests that are compiled with `#machine_endpoint`, imported from `Tests.Compiler.ShippingMachineCommandTest`):
  | declaration | expected `shapeOf` | route / shape it represents |
  |---|---|---|
  | `ShippingMachineEntryTest.mThree` | `[bool, bits 4] → one (bits 4)` | machine route, three slots of two kinds, mixed Bool/BitVec arguments, one BitVec result |
  | `ShippingMachineEntryTest.twoFlag` | `[bool] → one bool` | machine route, Bool result taken from a structure-returning callee |
  | `ShippingMachineEntryTest.twoCnt` | `[bool] → one (bits 8)` | same callee, BitVec result |
  | `ShippingMachineEntryTest.linChk` | `[bool, bits 8, bool] → one (bits 8)` | IP-library machine (LIN checksum), three arguments |
  | `ShippingMachineCommandTest.plain` | `[bits 8, bits 8] → one (bits 8)` | combinational (non-machine) route |
  | `ShippingMachineEntryTest.twoHW` | `none` | user-structure result `TwoOut`: outside the fragment (extension of `ResShape` needed, DC-COVER) |
  | `ShippingMachineCommandTest.toggle`, `ShippingMachineEntryTest.linChkDefault` | `none` | closed `defaultDomain` declarations: no leading `DomainConfig` binder |
  Survey result, for THIS survey only: no corpus declaration with an open domain and a `Prod`-of-Signals result was found (the `.pair` constructor is exercised by the local battery `tB` only), and the machine-route declarations at `defaultDomain` are outside `sigShape?`.
  This is a coverage finding, not a claim about DC-COVER: whether such tops occur among the successful targets is unsupplied. Also: `ShapeMatches` holds for `mThree` against its generated `mThree.machineData` (`decide`), and fails for swapped argument order and for a wrong result shape.
- **CLOSURE**: explicit transitive walk over `ConstantInfo` types and thm/defn values and inductive constructors, following `Expr.proj` structure names (the Part A walk uses `getUsedConstants`, which does not return them); `Init`/`Std`/`Lean` constants are leaves; opaque/axiom bodies are reported, not followed.
  14 targets reach no constant whose name or module is `Tools.ShippingGen5{Sem,Acc,DataOf,Env,T2}*` or contains `ConstValueE`, `primTable`, `genP`, `genSem`, `dataOf`, `FG_COMPLETE`, and no axiom constant; the non-core modules reached are within a stated list of 29 (the `Pkg`/`MachineData`/`Signal` vocabulary of `Tools.ShippingGen2Defs`).
  Exact sets: `sigShape?`, `shapeOf`, `sigShape?_telescope`, `sigShape?_machOuts` reach exactly `Sparkle.Compiler.Elab` besides this file. Walk-depth: `DeclConnect` reaches `Pkg.src`, `Pkg.kD`, `MachineData.bsIn`, `DCGen`.
  Negative controls (all detected): a direct mention, a helper definition in another namespace, a helper theorem body, a projection through an alias (found via the alias and `FakeKit.x`), and a collector unit control on a raw `Expr.proj` (shows that `getUsedConstants` misses the structure name and `usedConsts` finds it). Clean controls (a definition and a theorem over `Nat`) report no violation.
  Limit: the control for a raw `Expr.proj` is a unit test of the collector on a hand-built `Expr`; no elaborated declaration in the check contains a proj-only mention.
- **Planned, not implemented** (waits on approval of §C.3 rev5 and on the owners): TYPE/MUTANT/CLOSURE for `FG_COND`/`FG_CONNECT` (binder table by `inferType` against `Start`, `RunsTo`, `TopShips`, `synthesizeCombinational*` as in rev4, now with NV-Post/NV-GP/NV-CV as `example`s, and a mutant with O1 dropped, one with O2 dropped);
  the `TopShips` body pin after S2 merges (§C.3 R3); the value closure of the final theorem (an explicit list of owner constants `genP`, `ConstValueE`, the prim table if any, `ReflectsAll`, `Post`, `TopShips`, with positive and negative controls so that a quiet substitution of a trivial `CV` or `GP` is detected).

## 4. Units of pure lemmas — Part A, the accepted abstract core (explicit shape parameters, R2)

Units U1-U5 and U6 are stated over an ABSTRACT interface so that they hold without `sigShape?`/`ShapeMatches` being defined (these
are parameters, R2): `{E N CI Pk : Type}`, `find : E → N → Option CI`, `Shape : Type`, `Ty : Shape → Type`,
`shapeOf : CI → Option Shape`, `Match : Shape → Pk → Prop`, `Obs : Pk → (sh : Shape) → Ty sh → Prop`,
`CV : E → N → (α : Type) → α → Prop`, `P : N → Option Pk`. The concrete instance (`CI := ConstantInfo`, `Shape := SigShape`,
`shapeOf := fun ci => if ci.levelParams.isEmpty then sigShape? ci.type else none`, `Match sh p := ShapeMatches sh p.d p.kD`, `Obs p sh v := ∀ i bools bits, sh.obs v i bools bits = p.src i bools bits`)
is the later file; the abstract file does not mention `Pkg`, `MachineData` or `sigShape?`.

```lean
def DCAt (env) (X) : Prop := ∀ p, P X = some p → ∃ ci sh (v : Ty sh), find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v ∧ Obs p sh v
def DCGen (env) (Tgt : N → Prop) : Prop := ∀ X, Tgt X → DCAt env X
def DCImp (env) (Tgt) : Prop := ∀ X, Tgt X → ∀ p, P X = some p → ∀ ci, find env X = some ci → ∀ sh, shapeOf ci = some sh → Match sh p → ∀ v : Ty sh, CV env X (Ty sh) v → Obs p sh v
theorem dcGen_iff               : DCGen env Tgt ↔ ∀ X, Tgt X → DCAt env X                      -- U1 (by Iff.rfl; recorded)
theorem dcGen_mono (h : ∀ X, Tgt' X → Tgt X) : DCGen env Tgt → DCGen env Tgt'               -- U2
theorem dcImp_of_empty : DCImp (CV := fun _ _ _ _ => False) env Tgt                         -- U3a
theorem not_dcGen_of_empty (hT : Tgt X) (hP : P X = some p) : ¬ DCGen (CV := fun _ _ _ _ => False) env Tgt     -- U3b
theorem dcImp_of_dcGen (hV2 : Functional CV) (hfind : ∀ ci ci', find env X = some ci → find env X = some ci' → ci = ci') : DCGen env Tgt → DCImp env Tgt   -- U4a
theorem dcGen_of_imp_exists (hImp : DCImp env Tgt) (hEx : ∀ X, Tgt X → ∀ p, P X = some p → ∃ ci sh (v : Ty sh), find env X = some ci ∧ shapeOf ci = some sh ∧ Match sh p ∧ CV env X (Ty sh) v) : DCGen env Tgt   -- U4b
theorem dcAt_of_acc {R : N → N → Prop} (hstep : ∀ X, (∀ c, R c X → Ready c) → Ready X) : ∀ X, Acc R X → Ready X      -- U5
theorem dcGen_of_rows (hAcc : ∀ X, Tgt X → Acc R X) (hclosed : ∀ X c, Tgt X → R c X → Tgt c)
    (hstep : ∀ X, Tgt X → (∀ c, R c X → Tgt c → DCAt env c) → DCAt env X) : DCGen env Tgt      -- U6 (INTERMEDIATE)
```
(U4a: `find` is a function, so two `ci` for X coincide — a hypothesis, supplied by `Environment.find?` being a function at the concrete
instance, `rfl`.) `hstep` is the UNSUPPLIED content of rows 0-4 (§C.7); U6 is the Acc assembly only and is reported as "skeleton, rows
unsupplied". The old "U7 = DCF" is now §C.6 (DCF); no Lean for it in this freeze.


### 4.1 The audit in `Tests/Gen5/DeclConnectAbsCheck.lean` (rev3)

Exactly what is checked, and its limits:
- **TYPE.** For each of U1, U2, U3a, U3b, U4a, U4b, U5, U6 an independently written `Prop` (`ExpU*`, fully unfolded, not using `DCAt/DCGen/DCImp/Functional`) is compared with the theorem's type by `isDefEq` after instantiating the leading implicit type parameters. Positive control: the comparison must succeed.
- **MUTANT.** Per theorem one well-typed statement (`MutU*`) that differs from `ExpU*` in one place is built, and the same comparison must FAIL: U1 `∀`→`∃` on the right; U2 inclusion reversed; U3a conclusion is the `DCGen`-shaped (existence) form; U3b negation dropped; U4a `Functional` premise dropped; U4b existence premise `hEx` dropped; U5 `R c X` reversed to `R X c`; U6 `hAcc` dropped. These are signature/defeq rejections, NOT semantic counterexamples. The unit U4b-without-`hEx` also has a refutation `example` (empty relation). U6's `_hclosed` is UNUSED in the proof; no claim is made that U6 without it is unprovable or that dropping it is rejected for a semantic reason, and it has no mutant here.
- **AXIOMS.** `checkAxioms` on the eight theorems.
- **CLOSURE (direct + transitive).** From each theorem, a walk over the environment reading ConstantInfo bodies explicitly: `thmInfo.value`, `defnInfo.value`, types of every kind, constructors of inductives. `opaqueInfo` and `axiomInfo` are BOUNDARIES: their bodies are not followed and they are reported as UNTRACKED. A reached constant must belong to a module under `Init`/`Std`/`Lean` or to `Tools.ShippingGen5DeclConnectAbs` (no constant of the Check file itself, and no name containing `Pkg`, `MachineData`, `sigShape`, `ConstantInfo`, `GenPInv`, `DataSoundAt`, `dataOf`, `genP`, `Laws`, `T1Hyp` outside core). Negative controls (must be detected): a direct mention, a mention through a helper definition, through a helper theorem body, and an opaque boundary. This is a statement about the Lean constants the eight theorems reach in the elaborated environment; it is not a claim about any other file.


## 5. Open questions for the reviewer (Part C)

- **Q1** coverage of `sigShape?` on the successful targets (DC-COVER) and the extension of `ResShape` (struct, packed tuple, tuple input) — after the corpus tops are named.
- **Q4** the prim table (§C.6): definition vs trusted statement — user item only if adopted; `scripts/gen5/DC_CONNECT_PRIM_TABLE_DECISION.md`.
- **Q6** (closed by rev4) `DataSoundAt`'s `initOk` clause is `p.d.initOk (initsOf p.d) = true` (§C.4); whether DG-DATAOF's final `initsOf` keeps that name and namespace is its owner's.
- **Q7** (narrowed by rev4) `D`/`b` types are fixed (§C.3). Open: the form of `Post` (`b ↔ raw`), which is M4's; the reviewer is asked whether `∀ raw, Post b raw → …` is the acceptable carrier until M4 fixes it.
- **Q8** U-UNIV: is editing the `variable` line of the accepted `Tools/ShippingGen5DeclConnectAbs.lean` (and re-running its audit) acceptable, or should the concrete unit carry its own universe-polymorphic copy of U1-U6?
- **Q9** `ReflectsAll` has no Lean definition (§C.3). Is it acceptable as a parameter of `FG_CONNECT` (an INTERMEDIATE statement) until M4?
- **Q10** (new, R1) Is the split `FG_COND` (conditional schema) / `FG_CONNECT` (adds O1 `∃ raw, Post b raw`, O2 package existence, same witness) the acceptable carrier of the final connection, and are NV-Post/NV-GP/NV-CV the right non-vacuity facts?
- **Q11** (new, R3) Is the explicit dependence on the R-G audit (a) acceptable until S2 merges, with the body pin (b) afterwards?

## 6. Decision items (not adopted; none is needed to approve this freeze)

It is not established that the prim table of §C.6 is a NEW TRUSTED boundary (rev5; rev4 called it a candidate). Background and options: `scripts/gen5/DC_CONNECT_PRIM_TABLE_DECISION.md` (rev5). No decision is requested now. Nothing in U-UNIV, U-SHAPE1/2, U-ENTRY, U-ROWS depends on it.

## 7. Not claimed

- No claim that `ConstValue`, `sigShape?` coverage, `DeclConnect` or any row is supplied, or supplyable by a specific route.
- No claim that FG, FG-REF or M5 is complete. `dcGen_of_rows` / `declConnect_of_rows` are intermediate Acc assemblies; `FG_CONNECT` is an intermediate parametrized statement until M4 defines `Post`/`ReflectsAll`.
- No claim that `ConstValueFunctional` follows from the prim table; no claim that a new TRUSTED boundary is, or is not, required (§C.6).
- No claim about the R-G `TopShips` beyond the dependence recorded in §C.3: it strengthens the no-clock guarantee, and the audit is S2's.
- Built (agent build, not a clean issue-linked build): U-UNIV, U-SHAPE1/2, U-ROWS and `DeclConnectCheck` at the SHAs of §C.8. Not Lean at all: `FG_COND`/`FG_CONNECT`, `EntryWitness`, `TgtRun`, `ConstValueFunctional`, `ConstValueE`, `DataSoundAt`.
- No claim about `DataSoundAt`'s elaboration, `AssignKit`, `genP`, or `ShapeMatches` on a real corpus package.
- DG-SEM, DG-DATAOF and DG-ACC are not done; their results enter only as premises named after their own freezes. S2 (`TopShips` R-G) is in review and is not decided here.
- No new law, TRUSTED boundary, FG or guarantee change; no edit of compiler/shared definitions.
- A mutant in the check is a signature/defeq rejection, not a semantic counterexample.

## 8. Order

1. (Part A, done) abstract U1-U6 + check rev3.
2. (Part C, this review) approve the complete-type freeze §C.2-§C.8, including Q8/Q9.
3. U-UNIV, then U-SHAPE1/U-SHAPE2 (pure, in new files), then U-ROWS; the Lean commit stays `doing`, "clean build is the coder's".
4. U-ENTRY after DG-ACC A1; DCF (rule design and minimal-table survey proceed now, no decision awaited; a separate decision only if a new TRUSTED boundary is concretely found necessary); the final connection waits for DG-SEM / DG-DATAOF / DG-ACC / DG-COVER / M4.

### R-audit note (agent g5dc-r7, Check only; Tools unchanged)
- `Tests.Gen5.DeclConnectCheck.walk` no longer skips a name with no `env.find?`: it records it, and `reach` throws `WALK FAILED … unknown names`. Controls (scratch environment, constants added without kernel checking): unknown root, helper value naming an unknown constant, helper type naming an unknown constant, plus a clean control. Existing users of `reach` (`DeclConnectCheck`, `FGCheck`) still pass; `DeclConnectAbsCheck`/others have their own walkers and are not affected.
- `Tests.Gen5.FGCheck` pins `TgtRun.top`/`TgtRun.call` against independent telescopes and rejects 6 mutants (signature comparison only).
- Scope unchanged: real `EntryWitness`/Post/ReflectsAll/GP/CV remain unsupplied; this is not completion of the Issue, M5 or FG.
