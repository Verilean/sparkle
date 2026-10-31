# M4 parametric: bridge unit 6 (`ParamBridgeLegal`) — freeze, complete types, supplier table

Issue `sparkle-gen4-parametric-supply`, branch `kjob/g4par-r22`, base c3a287c1 (= F2 approved 0ebbddc0, build par21w-0ebbddc0, + comment/doc-only BUILT sync). Docs only; Lean waits for approval of this freeze.
Words: "this survey did not find a route/supplier for X" = the cited sources were read and X was not found; it never says X is impossible or underivable. A "mutant" in a Check is a rejection by signature/defeq/elaboration, not a semantic counterexample. Nothing here discharges T, changes FG, adds a law/TRUSTED boundary/axiom, or edits production/shared files (Specialize.lean, Type.lean, Iface, Entry, Tools/ShippingGen2Defs.lean, T1Hyp, T1HypND, Elab*.lean are read only). M4 / FG are not complete.

## 1. Supplier table re-checked at c3a287c1 (sources: Sparkle/IR/Specialize.lean:18-175, Sparkle/IR/Type.lean:68-100, Tools/ShippingGen4ParamIface.lean:62-135, Tools/ShippingGen4ParamEntry.lean:243-340, UNIT4/UNIT5 freezes §1)

New observation (corrects the UNIT4/UNIT5 wording "private ... not nameable from a new file"): existing approved files already name file-private constants of `Specialize.lean` through the mangled constant `(Name.mkNum (`_private ++ `Sparkle.IR.Specialize) 0) ++ `Sparkle.IR.Specialize.<name>` — `specValidateBindings` (Iface:66-73, an `elab` term) and `unfold_spec_unchecked` (Entry:247-249, an `elab` tactic naming `specializeModuleUnchecked`). Same mechanism, no visibility edit, no axiom, no new TRUSTED boundary (it is name resolution; the resulting statements are checked by the kernel). I did not elaborate the same trick for `requirePositive` in this docs-only step; the Check of this unit will show it (if it fails, the unit stops and reports, see §4).

| row | needs | existing lemma / def that could supply it (real name) | status after this survey |
|---|---|---|---|
| B1 `DimExpr.evaluate θ e = evalM θ e` | equation/unfolding of `partial def DimExpr.evaluate` (Type.lean:68) | none (partial = opaque to the kernel, no equation lemma) | **未供給 / この調査で辿った候補経路では未供給** |
| B2 `specializeType` arm `.bitVectorDim` | B1 + unfolding of `partial def specializeType` | none (model side: `specTypeM_ok`, `specTypeM_hwTypeFromDim`) | 未供給 (同上) |
| B3 `specializeExpr` arm `.sliceDim` | B1 + unfolding of `partial def specializeExpr` | none (model side: `specExprM_*`) | 未供給 (同上) |
| B4a private `requirePositive` (Specialize.lean:42-44; non-partial, total) | name the private constant; case split on `value == 0` | `requirePositiveM` (SpecType) is its model; no agreement theorem yet | **closable from existing material (mangled name + `by_cases`): selected, §2 `requirePositive_eq`** |
| B4b private `validateBindings` (Specialize.lean:29-40; non-partial) — direction "success ⇒ facts about θ" | name it (`specValidateBindings`, Iface) + `Except`-`forIn` inversion | `LegalBinding` (Iface:91), `specializeDesign_ok_legal` (success ⇒ `LegalBinding`), `except_bind_ok'`, `mapM_forall2` (Entry) | **closable for `AllPos θ` and for coverage of declared parameters (§2 `legalBinding_allPos`, `legalBinding_covers`)**; the converse direction (facts ⇒ `LegalBinding`) is not selected |
| T `SpecSuccessAllPositive` | B1-B3 production links + per-declaration success | none | **未供給 / この調査で辿った候補経路では未供給**; membership of T in FG is the user's decision (not taken) |
| FG connection | T and/or Layer B | none | 未供給 |

Result: B1-B3 and T are NOT closed by this survey (each needs the unfolding of a `partial` function, or option D1-D3 of `PARAMETRIC_SPECSUCCESS_DECISION.md`; none adopted). B4a/B4b (the non-partial private functions) close from names already used by approved files. Port/stmt/module model lifts (`specializePort`, `specializeStmt`, `specializeModuleUnchecked` models) remain possible model-side units but link nothing to production; B4a/B4b are chosen first because they are the only rows that link to the REAL production code and they supply the `ha : AllPos θ` hypothesis that F1 (`specTypeM_ok`), F2 (`specExprM_ok`, `specExprM_startLength`) and D1 (`evalM_pos`, `sliceOK_order`) all take as an unproved premise. No new law / TRUSTED / shared-definition / compiler change is required, so nothing is stopped for a decision.

## 2. Unit selected: F3 = B4a/B4b production linkage (`legalBinding_allPos`, `legalBinding_covers`, `requirePositive_eq`)
Why first: it is the only candidate that connects a model-side premise (`AllPos θ`, `Bound` of parameter names) to the REAL `validateBindings` (success of the real `specializeDesign` ⇒ `LegalBinding` is already proved in Iface). It does not claim anything about `specializeType`/`specializeExpr`/`DimExpr.evaluate` (B1-B3 stay unsupplied) and does not make T or FG progress; it removes the premise "`AllPos θ`" from the list of premises left unsupplied for a legal binding.

New file `Tools/ShippingGen4ParamBridgeLegal.lean` (imports `Tools.ShippingGen4ParamIface` and `Tools.ShippingGen4ParamBridgeSpecType`); check `Tests/Gen4/ParamBridgeLegalCheck.lean`; `lean_lib` entries only in lakefile. Namespace `Tools.ShippingGen4ParamBridgeLegal`; `open Lean Elab Term Sparkle.IR.AST Tools.ShippingGen4ParamIface Tools.ShippingGen4ParamLayerA Tools.ShippingGen4ParamBridgeSpecType`. Complete text of the freeze-listed items (nothing elided):
```lean
-- the file-private `Sparkle.IR.Specialize.requirePositive context value`, by its mangled constant (same mechanism as Iface `specValidateBindings`)
elab "specRequirePositive " c:term:max v:term:max : term => do
  let n := (Name.mkNum (`_private ++ `Sparkle.IR.Specialize) 0) ++ `Sparkle.IR.Specialize.requirePositive
  let c ← elabTerm c (some (mkConst ``String))
  let v ← elabTerm v (some (mkConst ``Nat))
  Term.synthesizeSyntheticMVarsNoPostponing
  Meta.mkAppM n #[c, v]

-- B4a: the production `requirePositive` is the F1 model `requirePositiveM`, for every context and value
theorem requirePositive_eq (context : String) (value : Nat) :
    specRequirePositive context value = requirePositiveM context value

-- B4b-1: a legal binding has only positive values (the premise `ha` of specTypeM_ok / specExprM_ok / specExprM_startLength / evalM_pos / sliceOK_order)
theorem legalBinding_allPos {D : Design} {θ : List (String × Nat)} (h : LegalBinding D θ) : AllPos θ

-- B4b-2: a legal binding binds every declared retained parameter of every module (the `Bound` premise for `DimExpr.parameter`)
theorem legalBinding_covers {D : Design} {θ : List (String × Nat)} (h : LegalBinding D θ) :
    ∀ m ∈ D.modules, ∀ q ∈ m.parameters, ∃ v, θ.lookup q.name = some v
```
Types used: `LegalBinding (D : Design) (θ : List (String × Nat)) : Prop := specValidateBindings D.modules θ = .ok ()` (Iface:91); `AllPos (θ : Binding) : Prop := ∀ p ∈ θ, 0 < p.2` (LayerA:43, `Binding = List (String × Nat)`); `requirePositiveM (context : String) (value : Nat) : Except String Nat` (SpecType:14); `Module.parameters : List Parameter` with `Parameter.name : String`.

Proof plan: `requirePositive_eq`: unfold the private constant (a tactic `elab` naming it, as `unfold_spec_unchecked`), `by_cases value == 0`, `simp`. `legalBinding_allPos`/`legalBinding_covers`: unfold `validateBindings` (private constant by mangled name), peel `validateParameterDeclarations`, the duplicate test and the two `for` loops with `except_bind_ok'` and one new helper `forIn_except_each : forIn l init f = .ok r → ∀ a ∈ l, ∃ s, f a ... = .ok s` (induction on `l`, outside the freeze list; stated against the exact `ForIn` shape produced by the elaborator); per-element `if value == 0 then throw` / `if bindings.lookup name |>.isNone then throw` are decided by `simp`. The helper's exact statement depends on the do-notation elaboration of Specialize.lean:35-39 and is fixed when the file is first elaborated; the three theorem types above do not change. If the `forIn` shape defeats this plan, the unit reports "route not completed in this attempt" with the failing goal and does NOT weaken the theorem statements.

## 3. Check (`Tests/Gen4/ParamBridgeLegalCheck.lean`), written from this text (same requirements as F1/F2)
- **Independent Expected**: `ExpReq : String → Nat → Except String Nat` (written in the Check from Specialize.lean:42-44, not `open`ing the Tool), `ExpLegal` (the predicate "no binding value is 0 ∧ every declared parameter name has a binding") compared by: `∀ c v, requirePositiveM c v = ExpReq c v`; theorem statements compared by `withReducible isDefEq` on `inferType` against independent copies; the elab term's elaborated type compared with `String → Nat → Except String Nat`.
- **Def mutants** (well-typed single changes only, signature/defeq rejection, not semantic counterexamples; single and compound reported separately): single: `requirePositiveM` `== 0` -> `≠ 0`; `== 0` -> `== 1`; error message text changed; returns `.ok 0`. Compound: both the test and the message changed. Counts are measured and reported separately by the rule "top-level `#...` directive lines per kind"; ill-typed/elaboration failures are NOT counted as mutants.
- **Theorem mutants** (well-typed): `legalBinding_allPos` `0 < p.2` -> `p.2 < 5`; `legalBinding_allPos` conclusion `AllPos θ` -> `AllPos (θ.reverse.tail)`; hypothesis `LegalBinding D θ` dropped; `legalBinding_covers` `∃ v` -> `∀ v`; `requirePositive_eq` RHS `requirePositiveM c v` -> `.ok v`. Rejection by type, as in F2.
- **AXIOMS**: `propext` / `Classical.choice` / `Quot.sound` only, for the 3 theorems (`collectAxioms`). **CLOSURE**: reuse the `ParamBridgeSpecExprCheck` detector: explicit `thmInfo/defnInfo` value traversal; unknown names fail; root judged itself; positive and negative controls: an unknown root, an unknown helper value, an unknown helper type; clean control; fixtures under `withoutModifyingEnv`; opaque bodies (reached: `String.Internal.append`) are typed-only and logged. No `sorry`, no `native_decide`. The Check imports only the Tool plus `Lean`. The Check is built on the exact tree to be committed; planned numbers are not results.
- Build: `kjob lake build Tests.Gen4.ParamBridgeLegalCheck` (incremental). After the Lean commit the issue stays `doing` with "clean build is coder"; review follows the coder's clean issue-linked build.

## 4. Open and unchanged
B1, B2, B3, T, Layer B, port/stmt/module/design model lifts, source/clock/PostTransfer/FG connection: OPEN. Issue not complete. No guarantee change, compiler change, shared-definition edit, law, or TRUSTED boundary is proposed. If the mangled-name route for `requirePositive`/`validateBindings` fails in the Check, that is reported as "route not completed", not as impossibility.
