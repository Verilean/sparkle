# DC-CONNECT: DeclConnect on the actual source — abstract core (accepted scope) + Part C complete-type freeze for review (rev4)

Issue `sparkle-gen5-dc-connect` (parent `sparkle-gen5-decl-bridge`; units DC-FORM / DC-SUPPLY / DG-DECLCONNECT).
Base: `kjob/g5dc-r3` 08e97dba (abstract U1-U6 and check rev3: scoped approved by the reviewer; Part C reported as unfrozen, which was correct).
Design sources (read with `git show par/gen5-t2:...`, c398021c): `DGEN_FREEZE.md` rev2 §2.6 (cited `DGEN:§2.6`), `T2COVER_FREEZE.md` rev2 §2,
`DG_ENV_FREEZE.md` rev2.2, and `scripts/gen2/GENERAL_SPEC.md` (FG §1.1 lines 88-93, M5 lines 488-507, §6 table line 535).

**Revision rev4 (this revision; docs only, no Lean file is added or edited).** Part C is rewritten as a complete-type freeze PROPOSAL for review.
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
| **A. Accepted abstract core** | §4 U1-U6 in `Tools/ShippingGen5DeclConnectAbs.lean` and the audit `Tests/Gen5/DeclConnectAbsCheck.lean` | Lean written; clean issue-linked build dc3v-08e97dba exit 0; scoped approved at 08e97dba. Abstract; says nothing about the actual source. Change proposed by rev4: U-UNIV (§C.8), universe of `Pk` only, proofs unchanged |
| **C. Concrete design: complete-type freeze PROPOSAL** | §C.1-§C.8 | design text; no Lean committed. Every Lean block was elaborated in a local scratch file (not evidence, not committed); the three agreement lemmas of §C.2 are statements with scratch proofs absent except `outPorts_eq`. Submitted for freeze review now |

Reading rule: Part A can stay accepted without Part C. Part C is the object of this review; concrete Lean (`Tools/ShippingGen5DeclConnect.lean`) starts only
after the reviewer approves it.

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

## C.3 `FG_COMPLETE` (complete binders; owner-premises explicit)

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

**TopShips: S2 vs base.** `kjob/g2tc-s2` fa84af5d (R-G, in review) changes only the BODY of `TopShips` (the premises `∀ t, ins t "rst" = 0` and `∀ t st, seedIn b ins t st "clk" = 0` become `"rst" ∈ b.inputs.map (·.name) → ∀ t, ins t "rst" = 0` and `"clk" ∈ b.inputs.map (·.name) → ∀ t, ins t "clk" = 0`; diffed against the base text);
its signature `(p n declName b raw D)` is unchanged (a `diff` of the base and S2 `Tools/ShippingGen2Defs.lean` over the `TopShips` block shows only the doc comment and those two premises). `FG_COMPLETE` mentions `TopShips` only as a constant and does not unfold it,
so its text is the same under both versions; the meaning is the S2 one (weaker for modules without `clk`/`rst` inputs, equal for modules with both). This is S2's guarantee question, recorded here, not decided here.
Any check that pins the text of `ShippingGen2Defs.lean` must be re-pinned when S2 merges; this unit adds none.

**Owner-premises found by the binder audit (no Lean definition in this survey):**
- `ReflectsAll`: `git grep ReflectsAll` over `par/gen5-t2`, `par/gen3-induct`, `par/gen2-spec`, `kjob/g2tc-s2`, `kjob/g5do-r2`, `kjob/g5sm-u3`, `kjob/g5ac-309a33a9` and this tree finds it only in `.md` text (GENERAL_SPEC.md:92,98,483; DG_ENV_FREEZE.md:217,272). GENERAL_SPEC.md:98 says it is "fixed in M4". Parameter: `ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop`.
- `raw`: FG's text leaves `raw` free and says "(b, raw) related by the entry's post-processing" (:93, :100). The only Lean statements that bind `raw` take it from the CORE run and
  relate `b = dropZeroWidthModule raw ∨ b = mergeChecked (dropZeroWidthModule raw)` (`T1Stmt`, `Tools/ShippingGen2Defs.lean:357-365`). For the ENTRY run `(b, D)` the relation is M4's deliverable. rev4 binds `raw` universally under a relation parameter `Post : Module → Module → Prop` (`∀ raw, Post b raw → …`).
  Two other readings exist: `∃ raw` in the conclusion (adds an existence claim FG does not make) or a second `RunsTo (synthesizeCombinationalCore …)` premise (a different run). rev4 does not choose between a stronger `Post`; whichever M4 supplies must be satisfied by the actual entry, otherwise FG is shrunk. DeclConnect does not use `raw` at all (the two other conjuncts are independent of it).
- `Pk`: FG's `Pk` is a schema variable. FG-REF is `Pk := genP env₀`.

```lean
def ConstValueFunctional (CV : ConstValueRel) : Prop :=
  ∀ env c (α β : Type) (v : α) (w : β), CV env c α v → CV env c β w → α = β ∧ HEq v w

inductive TgtRun (P : Pkgs ι dom) (declName : Name) : Name → Prop     -- least predicate: declName, and the ordinary callees of reached names
  | top : TgtRun P declName declName
  | call {c : Name} {q : Pkg ι dom} (hc : TgtRun P declName c) (hq : P c = some q) (k : Nat) (hk : k < q.d.shape.insts.length)
      (ord : (q.d.shape.instOrigins.getD k .ord).child? = none) : TgtRun P declName (q.d.shape.insts[k]'hk).1

open Tools.ShippingEntrySoundness (RunsTo)
def FG_COMPLETE {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
    (ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop)
    (Post : Sparkle.IR.AST.Module → Sparkle.IR.AST.Module → Prop)
    (GP : Environment → Pkgs ι dom) (CV : ConstValueRel) (L : Laws mref cref) : Prop :=
  ∀ (declName : Name) (parameters : List (String × Nat)) (mctx : Meta.Context) (cctx : Core.Context)
    (w w' : Void IO.RealWorld) (b : Sparkle.IR.AST.Module) (D : Sparkle.IR.AST.Design),
    Start L mctx cctx w →
    (RunsTo (synthesizeCombinational declName) mctx mref cctx cref w (b, D) w' ∨
     RunsTo (synthesizeCombinationalWithParameters declName parameters) mctx mref cctx cref w (b, D) w') →
    ReflectsAll L declName parameters →
    (∀ raw, Post b raw → ∃ (p : Pkg ι dom) (n : Nat), GP (envAt cref w) declName = some p ∧ TopShips p n declName b raw D) ∧   -- FG with Pk := GP env₀ (FG-REF)
    ConstValueFunctional CV ∧                                                                                                   -- V2
    DeclConnect CV (envAt cref w) (GP (envAt cref w)) (TgtRun (GP (envAt cref w)) declName)
```
(Elaborates in scratch with `envAt` copied locally.) Instantiation at integration, none of which is a quantifier of the final theorem: `GP := fun env₀ => genP (K env₀) (hF env₀)` with DG-ACC's `genP`
(§C.5); `CV := ConstValueE PT₀` — the DCF unit's relation at the adopted table, so there is NO free `V3` (rev3's `ConstValueOk CV V3` is withdrawn: "any `V3`" is not the actual-source meaning);
`ReflectsAll`, `Post`: M4. `ConstValueOk` is then `ConstValueFunctional (ConstValueE PT₀)`, proved by induction when the table is functional in the `Name`, which is a property of the table (§C.6).

`env₀ := envAt cref w` is the START world's environment; `ReadsAt env₀ cref w` is E1 (`readsAt_self`). `parameters` appears twice, in the route disjunct and in `ReflectsAll`, as in FG. For a
parametric run `machineShape?` is `none` (`Elab.lean:5072-5075`: `symbolicMode || !parameters.isEmpty`), so `GP env₀ declName` may be `none`; then the first conjunct is FG's own conclusion failing for that
run, not a weakening of `DeclConnect`: `FG_COMPLETE` is FG's schema with `Pk := GP env₀` and is as strong as FG is there.

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
2. The functionality `ConstValueFunctional (ConstValueE PT)` follows by induction on the two derivations when `PT` is functional in the `Name` (one row per `Name`). So `ConstValueOk` is not a second assumption beyond the table.
3. The table is the only place the semantics is stipulated rather than derived. If its rows are accepted as a stated list, GENERAL_SPEC.md:505-506 ("G3-DECL … is a meta-level fact") and the reporting rule make it a NEW TRUSTED boundary: a USER decision. It is NOT adopted here; `scripts/gen5/DC_CONNECT_PRIM_TABLE_DECISION.md` is the decision document (what the table is, options, cost, recommendation, reversibility, what happens if undecided).
4. How small the table can be made is a survey item this survey did not run: how many distinct constants occur in the accepted `defnInfo` values of the corpus after maximal `const-unfold` is not measured. rev3's claim that "each prim entry corresponds to one reader node kind" is a hypothesis to check (TABLE-COVERAGE), not a result.
5. Not claimed: that `ConstValueE` is the true kernel semantics; that any table is complete; that the recursion is well-founded (it is an inductive family, so no termination claim is needed).

The inductive `ConstValueE` is NOT written in rev4 and its complete Lean (the `Dyn` universe design for terms-and-types, the valuation, the dependent `app`) is the DCF unit's own freeze, after the decision. What §C.2/§C.3 need from it is only the type `ConstValueRel` and `ConstValueFunctional`.

## C.7 Supplier table

Status columns: **Exists** = present in a Lean file; **Pure now** = a pure lemma this issue can write without any dependency; **Waits** = depends on an unfinished owner (SEM / DATAOF / ACC / COVER); **Unsupplied** = this survey found no source or route (not a claim of impossibility). `[S]` = in this tree (9d26005c base).

| need | supplier | status | notes |
|---|---|---|---|
| abstract `DCAt/DCGen/DCImp`, U1-U6 | `Tools/ShippingGen5DeclConnectAbs.lean` | **Exists** (approved, scoped) | `Pk : Type` must become `Type u` (U-UNIV) |
| `sigShape?` family, `Scalar`/`ResShape`/`SigShape`, `applyArgs`, `obs`, `outPorts`, `shapeOf`, `ShapeMatches` | §C.2 | **Pure now** | scratch-elaborated; no dependency |
| `sigShape?_telescope`, `sigShape?_machOuts`, `outPorts_eq` | structural induction on `Expr`; `cases` | **Pure now** | `outPorts_eq` proved in scratch |
| `applyArgs_nil/cons`, `SigShape.obs` unfolding | `rfl` | **Pure now** | |
| `DeclConnect := DCGen …` and its unfolding equation | §C.2 | **Pure now** (after U-UNIV) | `rfl` in scratch |
| `FG_COMPLETE`, `TgtRun`, `ConstValueFunctional` | §C.3 | **Pure now** as definitions | statement only; the proof is the whole issue |
| `env₀.find? X = some ci` | `entry₀`'s definition (DG-ACC §3) | **Waits** on the file that defines `entry₀` (A1) | pure once it exists; independent of C0 |
| `ci_of_readsAt`, `envR_of_readsAt` (E4/E5) | `Tools/ShippingGen5Env.lean:52,58` | **Exists** | evidence side only (`MachineDefines`), not DeclConnect's statement; needs C0 |
| `ReadsAt` at the run's worlds (C0) | DG-ENV | **Unsupplied** | DG_ENV_FREEZE §0 S1 |
| package exists, `p.d`, `p.decl`, `kD` | DG-ACC `genP`, `genP_generated`, `genP_decl`, `genP_d_edges`; DG-SEM `genSem_d/decl` | **Waits** (ACC freeze in review; SEM `genSem` no Lean) | |
| `Acc (CallRel K) X` | DG-ACC `acc_of_run` | **Waits**; `AccServedStmt`/`AccKeepChildStmt` have no producer | DG-ACC §10 |
| `DataSoundAt` | `Pkg.ok`/`Pkg.body_eq` [S]; `initOk_of_ok`, `dataOf_sound` DG-DATAOF | conj. 1-2 **Exists**; conj. 3 **Waits** | not used by U1-U6 or `FG_COMPLETE` |
| `GenWF`, coverage of `dataOf` on real runs | DG-COVER / WFCOVER | **Unsupplied** | |
| `sigShape? = some` on every successful target | DC-COVER | **Unsupplied** | if a corpus top is outside the fragment: extend `ResShape` with its meaning (struct, packed tuple, tuple input), never weaken the statement |
| row 0: `∃ α v, CV env₀ X α v` | `ConstValueE` (DCF) | **Unsupplied** | needs the table decision |
| row 1: unfolding `ci.value ↦ entryConst …` preserves `CV` | `entryConst` (`Elab.lean:5272`) is definition unfolding; `EntryDefines` (`ShippingInlineSoundness.lean:48-57`), `entry_kept` (`ShippingEntrySoundness.lean:1132`) relate Exprs and RUNS | **Unsupplied** (depends on `CV`) | |
| row 2 shape/body | `dataOf_sound` + `readTerm_sound` (`ShippingReaderTerm.lean:1129`), `readN_expr_sound` (`ShippingReaderApp.lean:356`) | **Waits** on DG-DATAOF / READKINDS | |
| row 3 quote/eval agreement per node kind | `ConstValueE`'s rows vs the reader's table | **Unsupplied** | one row per node kind |
| row 4 `src = obsR (stateLoop …)` | `X.machine_source` per declaration (`ShippingMachineCommand.lean:2599-2610`); `GenFacts.source` for a package | per declaration **Exists**; uniform **Unsupplied** | |
| row 5 calls | `Acc` induction (Part A U5/U6) and E1 at the `ext` position (T2COVER §1) | skeleton **Exists**; per-call step = rows 3+4 at the callee | memory entries: DC-SUPPLY |
| `Tgt X ⇒ P X = some p` | DG-PKGASSIGN (`genP_pkg`, DG-ACC §6) | **Waits** | |
| `Post`, `ReflectsAll` | M4 | **Unsupplied** | §C.3 |
| TopShips (R-G) | `kjob/g2tc-s2` | in review | not unfolded by DC |

## C.8 Units for the Part C implementation, and the audit plan

Order, each unit in a NEW file or the named edit, built one target at a time in the Pod, SHA recorded by a comment-only commit; per the issue rules the Lean commit stays `doing` with "clean build is the coder's".

| unit | content | needs | state |
|---|---|---|---|
| **U-UNIV** | `Tools/ShippingGen5DeclConnectAbs.lean`: `variable {E N CI : Type} {Pk : Type u} {Shape : Type} {Ty : Shape → Type}`; rebuild `Tests.Gen5.DeclConnectAbsCheck` and re-run its TYPE/MUTANT/AXIOMS/CLOSURE | Part A | edit of an accepted file, proofs unchanged; scratch copy elaborates |
| **U-SHAPE1** | `Tools/ShippingGen5DeclConnect.lean`: `Scalar`, `ResShape`, `SigShape`, `ArgsTy`, `applyArgs`, `SigShape.obs`, `outPorts/ports/ctor?`, `domAt/scalar?/resShape?/sigGo/sigShape?`, `shapeOf`, `ShapeMatches`, `MatchC`, `ObsC`, `DeclConnect`, `ConstValueRel`, `ConstValueFunctional`, `TgtRun`, `FG_COMPLETE` | U-UNIV, `Tools.ShippingGen2Defs` | text of §C.2, §C.3 |
| **U-SHAPE2** | `sigShape?_telescope`, `sigShape?_machOuts`, `outPorts_eq`, `applyArgs_nil/cons`, `ShapeMatches` decidability if needed | U-SHAPE1 | proofs; `outPorts_eq` has a scratch proof |
| **U-ENTRY** | `entry₀_find`: `entry₀ env₀ X = some E → ∃ ci, env₀.find? X = some ci ∧ E = entryConst …` | DG-ACC A1 (the file defining `entry₀`) | waits |
| **U-ROWS** | instantiate `dcGen_of_rows` at the concrete `DeclConnect` with the row statements as explicit hypotheses (same as U6, concrete types) | U-SHAPE1 | |
| DCF | `ConstValueE`, its freeze | decision on the table | after the decision document |
| final connection | `FG_COMPLETE (…) L` | DG-SEM/DATAOF/ACC/COVER, DCF, M4 | not before |

Audit plan for `Tests/Gen5/DeclConnectCheck.lean` (the same discipline as Part A §4.1):
- **TYPE** (independent `Expected`, not by unfolding): `FG_COMPLETE` is compared against an independently written `∀`-statement with the binder types of the §C.3 table; `DeclConnect`'s unfolding equation by `rfl`; `sigShape?_telescope`, `sigShape?_machOuts`, `outPorts_eq`, `applyArgs_cons` against independent statements; the binder TYPES of `FG_COMPLETE` are also compared to the signatures of `Start`, `RunsTo`, `TopShips`, `synthesizeCombinational`, `synthesizeCombinationalWithParameters` by `inferType` (so a drift of a shared definition is caught, including after S2 merges).
- **MUTANT** (well-typed, one change; rejection by signature/defeq, NOT a semantic counterexample): `sigShape?` accepting any domain term (drops `domAt`); `applyArgs` starting at `q = 0`; `Scalar.obs .bool` as `toNat`-less identity; `ShapeMatches` without the output conjunct; `ShapeMatches` without `.domain ::`; `FG_COMPLETE` with `Post` dropped (raw free); `FG_COMPLETE` with `TgtRun` replaced by `fun X => X = declName` (narrower `Tgt`); `DeclConnect` with `∃ v` replaced by `∀ v` (the implication form); `shapeOf` ignoring `levelParams`. Each must FAIL the comparison with its `Expected`; each is reported as a signature/defeq rejection.
- **Behavioural controls** for the executable part (run with `#eval`/`run_cmd` in the check, output recorded): `sigShape?` on the seven declarations of §C.1 (two accepted, five rejected), and on one corpus declaration per `ResShape` constructor once the corpus is named by the reviewer.
- **AXIOMS**: `checkAxioms` on every theorem; `sorryAx` count 0.
- **CLOSURE**: the same explicit transitive walk over `ConstantInfo` bodies as Part A with the same negative controls (direct mention, helper def, helper theorem, opaque); the walk must reach no constant of DG-SEM/DG-DATAOF/DG-ACC from U-SHAPE1/U-SHAPE2 (these are pure), and must reach only `Tools.ShippingGen2Defs`/`Pkg` constants from `FG_COMPLETE`'s definition. No `V3`-like free relation parameter may remain in the final instantiation (`CV` is the constant `ConstValueE PT₀`): a CLOSURE negative control for that.
- **Value closure for the final theorem** (when it exists): an explicit list of the owner constants it reaches (`genP`, `ConstValueE`, `primTable₀`, `ReflectsAll`, `Post`) with positive and negative controls, so a quiet substitution of a trivial `CV` or `GP` is detected.


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
- **Q9** `ReflectsAll` has no Lean definition (§C.3). Is it acceptable as a parameter of `FG_COMPLETE` until M4?

## 6. Decision items (not adopted; none is needed to approve this freeze)

The prim table of §C.6 is a candidate NEW TRUSTED boundary. Decision document: `scripts/gen5/DC_CONNECT_PRIM_TABLE_DECISION.md`. Nothing in U-UNIV, U-SHAPE1/2, U-ENTRY, U-ROWS depends on the outcome.

## 7. Not claimed

- No claim that `ConstValue`, `sigShape?` coverage, `DeclConnect` or any row is supplied, or supplyable by a specific route.
- No claim that FG, FG-REF or M5 is complete. `dcGen_of_rows` is an intermediate Acc assembly.
- No claim that the Lean of Part C is built: it was elaborated in a local scratch file only (not committed, not evidence); the agreement lemmas except `outPorts_eq` have no proof yet.
- No claim about `DataSoundAt`'s elaboration, `AssignKit`, `genP`, or `ShapeMatches` on a real corpus package.
- DG-SEM, DG-DATAOF and DG-ACC are not done; their results enter only as premises named after their own freezes. S2 (`TopShips` R-G) is in review and is not decided here.
- No new law, TRUSTED boundary, FG or guarantee change; no edit of compiler/shared definitions.
- A mutant in the check is a signature/defeq rejection, not a semantic counterexample.

## 8. Order

1. (Part A, done) abstract U1-U6 + check rev3.
2. (Part C, this review) approve the complete-type freeze §C.2-§C.8, including Q8/Q9.
3. U-UNIV, then U-SHAPE1/U-SHAPE2 (pure, in new files), then U-ROWS; the Lean commit stays `doing`, "clean build is the coder's".
4. U-ENTRY after DG-ACC A1; DCF after the table decision; the final connection waits for DG-SEM / DG-DATAOF / DG-ACC / DG-COVER / M4.
