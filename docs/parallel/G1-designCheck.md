# G1: `designCheck` — inventory of its conjuncts (branch `fix/opt-fallback`, round optfb-3)

Status: read from the definitions. The Lean file
`Tools/ShippingChecksDesign.lean` was NOT built at the time of writing.
Statements marked "not traced" were not read to the bottom.

`designCheck (childMap D.modules) n (checkedOptimize b)` is the last
not-allowed antecedent of the generated depth SV endpoint
`f.machine_design_noShipsNoMaskedNR{n}_closed`. Write `C = childMap D.modules`,
`o = checkedOptimize b`.

## Definition (`Tools/ShippingDesignSV.lean` 103–124, `Tools/ShippingDesignSVLeaf.lean` 21–22, 40–100)

    designCheck C 0     o = textCheckI C o && kidsPass C leafCheck o.body
    designCheck C (n+1) o = textCheckI C o && kidsPass C (designCheck C n) o.body

    textCheckI C o =
      o.body.all seqStmtOkI &&                                      -- 1
      seqCheck (wofOf o) (weS o) o.body &&                          -- 2
      (seqNames o.body).all (fun x => declWidth o x == weS o x) &&  -- 3
      linkedWF C o.body &&                                          -- 4
      decide (instNames o.body).Nodup &&                            -- 5
      noSelfRead C o.body &&                                        -- 6
      portsMatchB C o &&                                            -- 7
      o.body.all (inst mn _ _ ⇒ (C mn).isSome)                      -- 8

    kidsPass C f body =
      body.all (inst mn _ _ ⇒ match C mn with | some (child, _) ⇒ f child | none ⇒ false)

    leafCheck m =
      m.body.all seqStmtOkA && m.body.all memOpsRefs &&             -- 9a
      (leafNames m.body).all (fun x => declWidth m x == weS m x) && -- 9b
      (if hasSyncMem m.body then seqCheckM (wofOf m) (weS m) m.body
       else seqCheck (wofOf m) (weS m) m.body)                      -- 9c

* `wofOf m = moduleWof m` (`Tools/SVParser/RoundtripProof.lean` 3313): the
  emitter's width map — wires ++ inputs ++ outputs looked up by SANITIZED
  name, `bitVector w ↦ w`, `bit ↦ 1`. `weS m = weOf (wofOf m)` (`getD 0`).
* `seqCheck wof we` (`Tools/SVParser/EmitSem.lean` 4331), per statement:
  assignment `l := r`: `sanitizeName l == l`, `wof l == some (we l)`,
  `widthOf we r == we l`, `sf4Check wof we r`; register: `wof out == some (we out)`,
  `widthOf we input == we out`, `sf4Check wof we input`; a memory only when
  combinationally read.
* `sf4Check` (2539): membership of an expression in the forward fragment
  `SF4` — every referenced name sanitize-stable and declared, constants of
  positive width, the operator shapes the emitter prints.
* `portsMatchB C o` (DesignSV 64): for every connection `(port, .ref w)` of
  every instance, `weS o w == weS child port`.

## Classification

Classes: (i) structure of the shipped module, from `RunFacts` /
`core_shipped_facts` / the guards; (ii) about the CHILDREN's modules, from
the real child's run; (iii) a check on EMITTED TEXT (the emitter's width
map, name sanitization, fragment membership); (iv) depth bookkeeping.

| # | Conjunct | Class | Status |
|---|---|---|---|
| 1 | `o.body.all seqStmtOkI` | (i) | DERIVED `core_design_kinds`: `linkedWF` is `false` on a memory (`seqStmtOkI_of_linkedWF`), and conjunct 4 holds |
| 2 | `seqCheck (wofOf o) (weS o) o.body` | (iii) | hypothesis `htext` of `core_designCheck_rest` |
| 3 | `declWidth o x == weS o x` on `seqNames o.body` | (iii), width tables | hypothesis `hwidths` |
| 4 | `linkedWF C o.body` | (i) | DERIVED `core_design_linked` (`core_shipped_facts`: fallback ⇒ the run's `core_linkedWF`; accepted ⇒ guard G2, `linkedWFX_sound`) |
| 5 | `(instNames o.body).Nodup` | (i) | DERIVED `core_design_names` (`core_shipped_facts`: guard G4) |
| 6 | `noSelfRead C o.body` | (i) | DERIVED `core_design_self`: `RunFacts.self` on `b` (`core_raw_facts`), moved along the instance statements, which `o` shares with `b` under the gate (`checkedOptimize_inst_iff_gate`) |
| 7 | `portsMatchB C o` | (iii) + (ii) | hypothesis `hports` |
| 8 | every instance resolves in `C` | (i) | DERIVED `core_design_resolve` (`linkedWF_inst`) |
| 9a | child: `seqStmtOkA`, `memOpsRefs` | (ii) | not assembled; within reach (below) |
| 9b | child: `declWidth c x == weS c x` on `leafNames` | (iii), on the child | inside hypothesis `hkids` |
| 9c | child: `seqCheck` / `seqCheckM` | (iii), on the child | inside hypothesis `hkids` |
| R | depth `n+1`: `kidsPass C (designCheck C n)` | (iv) | the same table one level down, per child; inside `hkids` |

"DERIVED" means: stated and proved in `Tools/ShippingChecksDesign.lean`
from `RunFacts C b`, which `core_runFacts` derives from the core run — NOT
YET BUILT. The structural part {1, 4, 5, 6, 8} of `textCheckI` then has no
check premise; what remains is {2, 3, 7} of the shipped module and the
children's check.

## What is stated in Lean (`Tools/ShippingChecksDesign.lean`)

    seqStmtOkI_of_linkedWF : linkedWF C body = true → body.all seqStmtOkI = true
    core_design_kinds / _linked / _names / _self / _resolve :
      RunFacts C b → <conjunct 1 / 4 / 5 / 6 / 8 of textCheckI C (checkedOptimize b)>
    textCheckI_of : the eight conjuncts → textCheckI C o = true
    kidCheck C 0 = leafCheck,  kidCheck C (k+1) = designCheck C k
    designCheck_eq : designCheck C n o = (textCheckI C o && kidsPass C (kidCheck C n) o.body)
    core_designCheck_rest (h : RunFacts C b) (n : Nat)
      (htext   : seqCheck (wofOf o) (weS o) o.body = true)
      (hwidths : (seqNames o.body).all (fun x => declWidth o x == weS o x) = true)
      (hports  : portsMatchB C o = true)
      (hkids   : kidsPass C (kidCheck C n) o.body = true) :
      designCheck C n o = true            -- o = checkedOptimize b

`core_designCheck_rest` is not yet used by a head: replacing the
`designCheck` antecedent of `machine_design_noShips_noBd` by these four
would only rename the gap (four Bool antecedents instead of one).

## The gaps, one by one

### 2 — `seqCheck` of the shipped module (class iii)

Four facts per assignment / register of `o.body`:

* (2a) `sanitizeName l = l` for assignment targets and for every referenced
  name (inside `sf4Check`). EXISTS for the scalar route only:
  `Tools.ShippingSVBridge.sanitizeName_of_clean` (a `Clean` name is
  sanitize-stable) and `synthesized_names` (every WIRE of a module the full
  entry returns on an `EnvDefines … (quoteDecl …)` declaration is
  sanitize-stable). MISSING for the machine route: the same statement over
  `MachineDefines`. Whether the closing proofs' `Allocated` invariant
  already covers the closed machine's wires was not traced. Port names (the
  declaration's binders, the result fields) come from the source: for them
  this is a condition on the data (a decidable `Clean` test of the names in
  `d.shape.binders` / `d.shape.layout.outs`), not a theorem.
* (2b) `wofOf o l = some (weS o l)`, i.e. `wofOf o l` is `some _`: `l` is
  declared with a `bitVector` / `bit` type among wires ++ inputs ++ outputs.
  MISSING: every assignment target, register output and referenced name of
  `o.body` is declared in `o`. For the accepted candidate the wires are a
  SUBLIST of `b`'s (`checkedOptimize_wires_sublist`), which is the wrong
  direction for declaredness; whether `refineCheck` on the extracted pair
  has a declaredness conjunct was not traced.
* (2c) `widthOf (weS o) r = weS o l`: width typing of every assignment and
  register input. The scalar route has `SizedExpr`
  (`Tools/ShippingSVBridge.lean` 53–104) and `TypedExpr`
  (`Tools/ShippingTypedExprSoundness.lean`). MISSING for the machine route:
  `SizedExpr` / `TypedExpr` of every right-hand side of the closed
  machine's body at its target's declared width.
* (2d) `sf4Check (wofOf o) (weS o) r`. THE PRINTER LEMMA NEEDED EXISTS, per
  expression: `SizedExpr.forward` (SVBridge 88) and `TypedExpr.forward`
  (TypedExprSoundness 236):

      TypedExpr we e n → (∀ x ∈ refsOf e, sanitizeName x = x ∧ wof x = some (we x)) →
        sf4Check wof we e = true

  What is missing is its hypotheses for the machine route: (2a), (2b), (2c).

Files read: `Tools/ShippingPrintSoundness.lean` (`emitExpr_render`,
`emitBody_render`, `checkedOptimize_printShape`),
`Tools/ShippingModulePrintSoundness.lean` (`emitModule_render`,
`acceptedOptimizer_module_render`), `Tools/ShippingSVBridge.lean`
(`synthesized_printCheck`, `synthesized_forwardCheck`,
`compiled_forwardCheck`: the text check DERIVED from the run, through the
optimizer's arms). All of them are stated for the scalar entry
(`EnvDefines`, `FExpr`); `forwardCheck` is `false` on any non-assignment
statement. Nothing of this kind was found over `MachineDefines` or for a
body with registers / instances (grep for theorems concluding
`seqCheck … = true` / `sf4Check … = true` outside `Tools/SVParser`: only the
two `forward` lemmas).

The missing statement:

    theorem core_seqCheck (… the hypotheses of core_runFacts …)
        (hclean : <the Clean test of the declaration's port names>) :
        seqCheck (wofOf (checkedOptimize b)) (weS (checkedOptimize b))
          (checkedOptimize b).body = true

Its two halves: (I) the statement on `b`, from the run; (II) the accepted
candidate: `hierRefineCheck b o' = true → seqCheck … b.body → seqCheck … o'.body`.
(II) does not follow from `hierRefineCheck` as far as its definition shows
(it validates instance statements, connections and `refineCheck` on the
extracted pair; no conjunct is about `SF4` membership of `o'`'s
right-hand sides — `refineCheck`'s own conjuncts were not read for this).
The scalar route proves its analogue for its optimizer arms
(`checkedOptimize_printCheck`). Two ways: a lemma that `optimizeModule` +
`deinline` preserve `seqCheck`, or a FALLBACK guard in `checkedOptimize`
(return `b` when `seqCheck` of the candidate fails) — a compiler edit of the
kind this branch made for `linkedWFX`; a decision for the user.

### 3 — the width tables agree on `seqNames` (class iii)

`declWidth o x` and `weS o x` read the declarations by raw and by sanitized
name respectively (`declWidth`'s definition was not re-read here; conjunct 3
exists because the two can differ). Equal when the names used are declared
once and sanitize-stable: (2a) + (2b) + duplicate-free declared names.
MISSING (pure; not found): 

    (∀ p ∈ decls m, sanitizeName p.name = p.name) → (decls m).map name |>.Nodup →
      x ∈ (decls m).map name → declWidth m x = weOf (moduleWof m) x

(`Tools.ShippingSVBridge.find_sanitized`, `printWidths_wire` are its
counterparts over `printWidths` for the scalar route.)

### 7 — `portsMatchB` (class iii + ii)

Content: the parent wire of a connection and the child's port have the same
emitted width.

* OUTPUT connections: `RunFacts.wid` (`instOutWidthsOk`,
  `core_instOutWidthsOk`, with the per-child `hkidW`) is this fact over
  `declWidth` of the parent and the child port's type; it moves to
  `weS`/`weS` by lemma 3 on both modules.
* INPUT connections (argument ports, `clk`, `rst`): nothing is derived.
  MISSING: for a call statement, the wire connected to an argument port `q`
  of the child has `q`'s width — the argument-side analogue of
  `core_callPorts` / `hkidW` (`Tools/ShippingChecksWidths.lean`). As with
  Finding A, no compiler pass was found that compares the two, so it would
  be a decidable data condition per parent/child pair (an analogue of
  `callWidthsOk`).

### 9a — children's statement kinds (class ii)

`ChildIfaceG.seqOk : b.body.all seqStmtOk = true`
(`Tools/ShippingSeqChildIface.lean` 50; from the real leaf child's run by
`seqChild_of_real`) gives `seqStmtOkA` (assignments and registers are two
of its three kinds) and `memOpsRefs` (`true` on every non-memory statement).
Two short pure lemmas, NOT written: they are of no use alone, 9b / 9c are
conjuncts of the same Bool.

### 9b, 9c — children's text check (class iii)

Lemma 3 and gap 2 for a leaf machine's returned module: the same missing
statements, over a run of the full entry on a machine WITHOUT calls (in the
style of `leaf_run_masked`). The child's module is what its own full entry
returned (the `RealChild` witness), so half (I) is needed there, and half
(II) for the optimizer arm that applies to a register body (`seqStmtOk`
branch: `refineCheck m o`).

### R — depth (class iv)

`kidsPass C (designCheck C n)`: each child with calls needs this whole table
for ITS module on the SAME child map `C`. Bookkeeping in the style of
`outsCheck_design` (`Tools/ShippingChecksDepth.lean` 41): if every module of
the design passes `textCheckI C` and every instance-free one `leafCheck`,
every depth follows. NOT stated: it needs gaps 2, 3, 7 for every module of
the design.

## Summary

* Derived (unbuilt), no check premise: conjuncts 1, 4, 5, 6, 8.
* Real gaps, emitted text: 2, 3, 7 of the shipped module; 9b, 9c of the
  children. They reduce to these missing statements:
  (A) the machine route's names are sanitize-stable (allocated wires: a
      theorem; source port names: a data condition);
  (B) written / read names are declared in the shipped module;
  (C) the closed machine's right-hand sides are width-typed (`SizedExpr` /
      `TypedExpr`) at their targets' declared widths — the hypothesis of the
      existing printer lemmas `SizedExpr.forward` / `TypedExpr.forward`;
  (D) the accepted optimizer candidate stays in the fragment (a lemma about
      the optimizer, or a fallback guard);
  (E) the argument-side width agreement of a call (for conjunct 7).
* Within reach without new theory: 9a; lemma 3 given (A) and (B); the depth
  bookkeeping R.
