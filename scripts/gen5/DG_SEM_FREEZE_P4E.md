# DG-SEM freeze P4e — supplying `GenExtAtCall` (T2-TIE's `hDG_SEM`) from the U4 parts (docs only)

**FOR REVIEW — design only; no Lean edited, nothing elaborated.** Base `kjob/g5sm-u4` `1258f07e` (U4A–F scoped-approved; clean build `smu4v-1258f07e`, exit 0, 709 jobs).
All statements below are PROPOSALS until approved. `[B]` = built at the base, `[T]` = text read from `kjob/g5tt-cr6` `Tools/ShippingGen5T2Tie.lean:238`
(**not in the base**: `Tools.ShippingGen5T2Tie` is not importable from this branch), `[N]` = new here.
No new TRUSTED boundary/law, no FG/guarantee change, no shared-definition/compiler edit, no `GenWF` strengthening, no FG narrowing, no `sorry`/`axiom`/`native_decide`.

## 0. The target `[T]`

```lean
def GenExtAtCall (p q : Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length) : Prop :=
  ∀ (i : ι) (bools : Nat → Signal (dom i) Bool) (bits : (j : Nat) → (n : Nat) → Signal (dom i) (BitVec n))
    (k' : Nat) (o : OutField) (f : Nat → Nat),
    q.d.shape.layout.outs[k']? = some o → CallField p q k o →
    (q.src i (decA p q k hk i bools bits) (decB p q k hk i bools bits))[k']? = some f →
    SigAt (p.extBS i bools bits) (p.extS i bools bits) (p.kD + k)
      (((p.d.bsIn.drop p.kD)[k]?.map (·.2)).getD .domain) f
```
with `decA/decB` (`Tools/ShippingGen5T2Dec.lean`) `:= boolsOf/bitsOf (q.d.bsIn.take q.kD) (valsOf (p.lsrc i bools bits) (p.d.shape.insts[k]'hk).2.1)`, and
`SigAt bs vs pos κ f` := `.bits w ⇒ ∀ τ, (vs pos w).val τ = BitVec.ofNat w (f τ)`; `.bool ⇒ ∀ τ, (bs pos).val τ = (f τ != 0)`; `.domain ⇒ False`.

## 1. Route (real names) — what the U4 parts give, what is left

For `p` whose arm is `genSemGen Q X g` (`p.kD = kDOf g.d`, `p.extS = extOf Q g i bools bits Sst`, `p.extBS = extBOf …`, `p.lsrc = lsrcAt g.d (extBOf …) (extOf …) Sst` by `lsrcAt_genSemGen` `[B]`, `Sst := stateLoop …`):

| step | content | from |
|---|---|---|
| (a) | the stage value at `kDOf g.d + k` of an ordinary call is `withCall … (calleeOut Q g i S st.1 st.2 k)` | `callOut` unfolded (new, mirrors `callOut_mem_val` `[B]`) → **U5A** |
| (b) | position `kDOf g.d + k` of the final stage = its value at stage `k+1` | `ExtStage_agree`, `ExtStage_succ` `[B]` |
| (c) | `calleeOut` read at stage `k` = `calleeOut` read at the final families (arguments are clean `let`s) | `rowC_at`, `lsrcAt_congr`, `ExtStage_agree` `[B]` (same pattern as `ext_mem_final`) → **U5B** |
| (d) | `calleeOut …` = the callee's `src` on the DECODED families, at the index `k'` selected by `CallField` | unfold `calleeOut`, `selIdx` → **U5C**, **U5D** |
| (e) | kind: `callKind g.d k ≠ .domain` | `RowB` (first conjunct) `[B]` ⇒ built into `GenWF`; `callKind g.d k = ((g.d.bsIn.drop (kDOf g.d))[k]?.map (·.2)).getD .domain` by `rfl` |
| (f) | non-memory origin: `(originOf p.d k).child? = none` (the first conjunct of `CallDec`) ⇒ `originOf ≠ .mem …` since `child? (.mem …) = some …` | `InstOrigin.child?` (`Sparkle/Compiler/MachInstOrigin.lean:28`) |
| (g) | package-level transport `p.toSem = genSemI (semOf P) X g` ⇒ `p.d = g.d`, `p.extS/extBS/lsrc` are those of `genSemGen`, and `(q.toSem).src = q.src`, `(q.toSem).d = q.d` | `Pkg.toSem`, `genSemI_d`, `SemPkg.src/…` `[B]` → **U5E** |

Not closed here, kept as NAMED PREMISES (never discharged by assumption inside a theorem; each appears as a hypothesis):

| premise | where | supplier (issue) / status |
|---|---|---|
| `hq : P (p.d.shape.insts[k]'hk).1 = some q` (the callee package of call `k`) | U5E | `sparkle-gen5-t2-tie`'s hDG_GENP / hDG_CLOSINGRUN; the callee-package supply is **not** here |
| `hnd : p.d.shape.instFields ≠ [] → (q.d.shape.layout.outs.map (·.name)).Nodup` (so `CallField` pins the index) | U5D, U5E | this survey **did not find** a supply route for a *package* `q` (a possible lead, **not** checked: `Sparkle/Compiler/Elab.lean:5085` rejects non-Nodup `outs` when the shape is built, and `Tools/ShippingReaderOutNames.lean` `machineShape?_outsTest`/`outsTest_facts`); owner would be DG-DATAOF / reader bridge. For `instFields = []` it is not needed (`outs = [o]` pins `k' = 0`) |
| `hp : p.toSem = genSemI (semOf P) X g` | U5E | which `g : GenIn` a package comes from = DG-DATAOF (`GenData.toIn`) / DG-GENP; the theorem is stated for *any* such `g` |
| `GenIn.wf`/`GenIn.ok` (`GenWF g.d`, `g.d.ok`) | U5B, U5E | they are fields of `GenIn` (`[B]`); their coverage for a real run is DG-WFCOVER, **not supplied** |
| `CallOutRange p q k hk` (`hDG_SEM_range`; the callee output is in range of the binder kind) | T2-TIE | **not part of this unit**; a callee-output range fact; this survey found no supply route (it is a fact about the callee's `src`, i.e. ACC/causality side) |
| causality of the callee `src` / `GenFacts.causal` (P6'), `Acc`, M5, FG | — | not supplied; not claimed |

**First unit to implement: U5B** (`calleeOut_final` + `ext_call_final_bool/bits`). Reason: it is the only step whose proof is not a definitional unfolding —
it repeats the `ExtStage_agree` + `lsrcAt_congr` + `rowC_at` argument of `ext_mem_final` for the `calleeOut` read, and everything else (U5A, U5C, U5D, U5E) is unfolding
or `Option`/`List` bookkeeping around it. U5A is its two-line prerequisite and goes in the same file. U5E (the `Pkg`-level wrapper) cannot be built before
`Tools.ShippingGen5T2Tie` reaches the base (it states `GenExtAtCall`); until then U5E stays a frozen statement only, and an *unfolded-conclusion* variant is not added (it would duplicate `GenExtAtCall`'s body).

## 2. Full types (new file `Tools/ShippingGen5SemExt.lean`, namespace `Tools.ShippingGen5Sem`, `set_option autoImplicit false`, imports `Tools.ShippingGen5SemMem`; same `open`s and variables as `Tools/ShippingGen5SemMem.lean` `[B]`: `{ι : Type} {dom : ι → DomainConfig}`)

### 2.1 U5A — the stage value of an ordinary call
```lean
theorem callOut_bool_val (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ .mem cb aw dw)
    (hκ : callKind g.d k = .bool) :
    (callOut Q g i S k st).1 (kDOf g.d + k) = ⟨fun τ => calleeOut Q g i S st.1 st.2 k τ != 0⟩

theorem callOut_bits_val (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat)
    (st : (Nat → Signal (dom i) Bool) × ((j n : Nat) → Signal (dom i) (BitVec n)))
    (c : Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ .mem cb aw dw)
    (hκ : callKind g.d k = .bits w) :
    (callOut Q g i S k st).2 (kDOf g.d + k) w = ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S st.1 st.2 k τ)⟩
```
Proof: `unfold callOut; rw [hk]; dsimp only; split` on `originOf`; the `.mem` branch contradicts `hno`; the other branches are `withCall … (callKind g.d k)`; `rw [hκ]`; `if_pos rfl`.
(The `match originOf g.d k with | .mem … | _` has the wildcard arm for `ord`/`field`; `hno` only removes `.mem`.)

### 2.2 U5B — the `calleeOut` read is stage-independent; the final families at `kDOf g.d + k`
```lean
theorem calleeOut_congr (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs bs' : Nat → Signal (dom i) Bool) (vs vs' : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (h : ∀ l ∈ callArgs g.d k, ∀ j, lsrcGet (lsrcAt g.d bs vs S) l j = lsrcGet (lsrcAt g.d bs' vs' S) l j) :
    calleeOut Q g i S bs vs k = calleeOut Q g i S bs' vs' k

theorem calleeOut_final (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (hkn : k < g.d.shape.insts.length) :
    calleeOut Q g i S (ExtStage Q g i bools bits S k).1 (ExtStage Q g i bools bits S k).2 k =
      calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k

theorem ext_call_final_bool (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ .mem cb aw dw)
    (hκ : callKind g.d k = .bool) :
    extBOf Q g i bools bits S (kDOf g.d + k) =
      ⟨fun τ => calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k τ != 0⟩

theorem ext_call_final_bits (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (bools : Nat → Signal (dom i) Bool) (bits : (j n : Nat) → Signal (dom i) (BitVec n))
    (S : Signal (dom i) (HList (tys g.d.ss))) (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder) (w : Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hno : ∀ cb aw dw, originOf g.d k ≠ .mem cb aw dw)
    (hκ : callKind g.d k = .bits w) :
    extOf Q g i bools bits S (kDOf g.d + k) w =
      ⟨fun τ => BitVec.ofNat w (calleeOut Q g i S (extBOf Q g i bools bits S) (extOf Q g i bools bits S) k τ)⟩
```
`GenWF`/`d.ok` are taken from `g.wf`/`g.ok` (fields of `GenIn`), so they are not separate hypotheses here (unlike `ext_mem_final`, which takes them as arguments; this is a deliberate
difference of form, not of content). Proof of `calleeOut_congr`: `unfold calleeOut`; `valsOf L (callArgs g.d k) = fun τ => (callArgs g.d k).map (…lsrcGet…)` by `funext`, rewritten with `h` (`List.map_congr_left`); the rest is `rfl`. Proof of `calleeOut_final`: as `ext_mem_final`'s `hl` — `rowC_at` (every `l ∈ callArgs g.d k` is `clean`), `lsrcAt_congr … k` with the `ExtStage_agree (n := k) (m := insts.length)` families, then `calleeOut_congr`.
Proof of the last two: (b) `ExtStage_agree` at `n := k+1`, `ExtStage_succ`, U5A, then `calleeOut_final`.

### 2.3 U5C/U5D — `calleeOut` as the callee's `src` on the decoded families
```lean
theorem callArgs_of_insts (d : MachineData) (k : Nat) (c : Name) (a : List Nat) (κ : MixedGateBinder)
    (hk : d.shape.insts[k]? = some (c, a, κ)) : callArgs d k = a

theorem calleeOut_eq_src (Q : Name → Option (SemPkg ι dom)) (g : GenIn) (i : ι)
    (S : Signal (dom i) (HList (tys g.d.ss)))
    (bs : Nat → Signal (dom i) Bool) (vs : (j n : Nat) → Signal (dom i) (BitVec n)) (k : Nat)
    (c : Name) (a : List Nat) (κ : MixedGateBinder) (q : SemPkg ι dom) (k' : Nat) (f : Nat → Nat)
    (hk : g.d.shape.insts[k]? = some (c, a, κ)) (hQ : Q c = some q) (hsel : selIdx g.d q k = some k')
    (hf : (q.src i (Tools.ShippingMachineChild.boolsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a))
                  (Tools.ShippingMachineChild.bitsOf (D := dom i) (q.d.bsIn.take q.kD)
                      (Tools.ShippingMachineCallsLinkedT.valsOf (lsrcAt g.d bs vs S) a)))[k']? = some f) :
    calleeOut Q g i S bs vs k = f

theorem selIdx_of_callField (d : MachineData) (q : SemPkg ι dom) (k k' : Nat) (o : Sparkle.IR.Machine.OutField)
    (ho : q.d.shape.layout.outs[k']? = some o)
    (hcf : if d.shape.instFields = [] then q.d.shape.layout.outs = [o] else o.name = d.shape.instFields.getD k "")
    (hnd : d.shape.instFields ≠ [] → (q.d.shape.layout.outs.map (·.name)).Nodup) :
    selIdx d q k = some k'
```
(`hcf` is `CallField`'s body with the `Pkg`s replaced by their data, so U5D does not depend on `Pkg`/`T2Tie`.) Proof of U5D: `instFields = []` ⇒ `outs = [o]` ⇒ length 1, `k' = 0`; otherwise `List.findIdx?` on a `Nodup`-by-name list returns the unique index.

### 2.4 U5E — the `Pkg`-level wrapper (statement frozen; implementation only after `Tools.ShippingGen5T2Tie` is in the base)
Imports `Tools.ShippingGen5T2Tie` (for `GenExtAtCall`, `SigAt`, `decA`/`decB`), `Tools.ShippingGen5SemPkg` (for `semOf`, `Pkg.toSem`).
```lean
theorem genExtAtCall_of_genSem {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hq : P (p.d.shape.insts[k]'hk).1 = some q)
    (hord : (originOf p.d k).child? = none)
    (hnd : p.d.shape.instFields ≠ [] → (q.d.shape.layout.outs.map (·.name)).Nodup) :
    Tools.ShippingGen5T2Tie.GenExtAtCall p q k hk
```
(namespace of `GenExtAtCall`/`decA` as in `[T]`; to be adjusted to the actual namespaces when imported.) Proof plan: from `hp`, `genSemI_d` and `hk` get `g.d.shape.insts ≠ []`, hence `genSemI … = .gen (genSemGen (semOf P) X g)`; injectivity of `SemPkg.gen`/`Pkg.toSem` at the `.gen` arm gives `p = .gen …` fields; transport `p.d`, `p.kD`, `p.extS`, `p.extBS`, `p.lsrc` to the `genSemGen` ones (the `SrcSem.extS/extBS/lsrc` are the same terms by `rfl`, `lsrcAt_genSemGen`); `hq` + `semOf` give `Q c = some q.toSem`; from `hord`, `hno`; from `RowB` (`g.wf`), `callKind g.d k ≠ .domain`, and `callKind g.d k` = the `SigAt` kind by `rfl`; case on it: `.bool` ⇒ `ext_call_final_bool`, `.bits w` ⇒ `ext_call_final_bits`, then `calleeOut_eq_src` (with `selIdx_of_callField`) rewrites `calleeOut` into `f`. **Known delicate point (to be checked when implemented, and reported if it fails):** the transport through `hp` of a `Pkg` (with its fact field) to a `SrcSem`.

## 3. Check (new file `Tests/Gen5/SemExtCheck.lean`, written from the sentences of §2, not from the implementation)
- **TYPE**: each theorem of §2.1–§2.3 (and §2.4 when it exists) is compared with an `Exp…` statement written independently in the Check from the prose of §2 (with the `Exp…` binders and the conclusion written in a different but defeq-checked form where natural), by the SAME reducible comparer as `Tests/Gen5/SemCallCheck.lean`.
- **DEFBODY** (new, answers the audit limit of 1258f07e): the definitions the new theorems depend on — `selIdx`, `calleeOut`, `withCall`, `callOut`, `ExtStage`, `extBOf`, `extOf`, `callKind`, `callArgs`, `originOf` (10) — are compared **by body** with independently written `ExpBody…` terms (same comparer on `ConstantInfo.value?`). If a body of a structurally recursive definition (`ExtStage`) is not comparable by the reducible comparer, it is compared by its equation lemmas' statements instead and the Check reports which of the 10 used which method. Counted separately from TYPE.
- **MUTANT**: well-typed single-change mutants only (a mutant that does not elaborate is not counted); at least: the conclusion's conjunct dropped (where a statement has one), a hypothesis dropped (`hno`, `hκ`, `hsel`, `hnd`), one place changed (`k`↔`k+1`, `.bool`↔`.bits`, `!= 0`↔`== 0`, `kDOf g.d + k`↔`kDOf g.d`). Rejection is by signature/defeq, **not** a semantic counterexample.
- **AXIOMS**: standard only (`propext`, `Classical.choice`, `Quot.sound`); **sorry** absent.
- **CLOSURE**: the explicit thm/defn/opaque constant walk from the new roots; unknown name ⇒ `throwError`. Unknown negative controls (**three**, as the audit requires): (1) an unknown *root*, (2) an unknown *helper value* (a theorem whose proof term reaches a missing helper constant), (3) an unknown *helper type* (a theorem whose statement mentions a missing constant), plus one **clean** control that must pass. Forbidden-constant controls as at 1258f07e.
- **REACH**: `ext_call_final_bool/bits` reach `callOut_bool_val/bits_val`, `calleeOut_final`, `ExtStage_agree`; `calleeOut_final` reaches `lsrcAt_congr`, `rowC_at`, `calleeOut_congr`; `calleeOut_eq_src` reaches `calleeOut`.
- Numbers are reported as real counts with the category and the counting rule next to them. Builds: Pod `kjob lake build Tools.ShippingGen5SemExt`, then `Tests.Gen5.SemExtCheck`, one at a time; the clean focused build is the coder's; the built SHA goes into the header by a comment-only commit.
- Lakefile: `lean_lib` entries for the two new files only.

## 4. Not claimed
- Not `GenExtAtCall` for any real package: U5E is conditional on `hp`, `hq`, `hord`, `hnd`, and on `GenIn` (hence `GenWF`/`d.ok`) existing for the run; none of these is supplied here.
- Not `CallOutRange`, causality, `Acc`, `GenWF`/`d.ok` coverage of real runs, DATAOF/ACC, M5, FG. Nothing here changes `T2-TIE`'s hypotheses; `hDG_SEM` is only *discharged* by U5E under the premises above.
- The route of §1 is read from the definitions; nothing is elaborated until U5A/B are built. MUTANT results are signature/defeq rejections, not semantic counterexamples.

## 5. Revision rev2 (answers reviewer changes_requested on 783419ad: R1, R2, R3) — supersedes the conflicting text of §0–§4

Reference fixed at **`783419ad`** (`kjob/g5sm-u6` base; in this tree `Tools/ShippingGen5T2Tie.lean`, `Tools/ShippingGen5T2Dec.lean`, `Tools/ShippingGen5T2Range.lean` exist and are importable —
the "not in the base" remark of the header/§0/§2.4 is withdrawn; the `[T]` mark now means "read at 783419ad").

### 5.1 R1 — existing supply is reused; no duplicate gap
* **`hnd`** (callee output names `Nodup`). For a **`Pkg`** `q`, it is supplied by `Tools.ShippingGen2.t2r_ok_outNames_nodup q.d q.ok : (q.d.shape.layout.outs.map (·.name)).Nodup`
  (`Tools/ShippingGen5T2Range.lean:238`; its hypothesis `q.d.ok = true` is the `Pkg` field `q.ok`). So at the Pkg level `hnd` is **not** a premise and not a gap; the earlier sentence
  "this survey did not find a supply route for a package q" and the lead on `Elab.lean:5085` / `ShippingReaderOutNames` are withdrawn for the Pkg case.
  U5D (`selIdx_of_callField`) is stated on a `SemPkg`/`MachineData` and keeps `hnd` as a hypothesis (a `SemPkg` carries no `ok` field); **U5E derives it from the `Pkg`**: `fun _ => t2r_ok_outNames_nodup q.d q.ok` (a corollary, not an assumption).
* **`CallOutRange p q k hk`**: not part of this unit and not a gap of DG-SEM. Existing: `Pkg.src_range q` (every source output `< 2 ^ o.width`, unconditional, `T2Range.lean:122`) and
  `callOutRange_of_widths p q k hk houtTy hW` (`T2Range.lean:162`; inputs `houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width` and `hW : CallOutWidthAt p q k`). What is **not supplied** is only the *run-level supply of those inputs*
  (`houtTy`, `hW` for each call of a real run), and it is not assigned to ACC/causality. This is the existing T2-TIE connection (`T2Conn.lean`); nothing new is allocated here.
* Table row replacement: premise `hnd` → *derived for Pkg (U5E corollary of `t2r_ok_outNames_nodup`), kept as a hypothesis of U5D only*; premise `CallOutRange` → *existing bridge; run-level supply of `houtTy`/`hW` OPEN, T2-TIE side*.
* Still premises of U5E (unchanged, **not** supplied here): `hq` (hDG_GENP/CLOSINGRUN), `hp` (which `g : GenIn`; DATAOF), `g.wf`/`g.ok` for a real run (WFCOVER), `hord`. Causality/`Acc`/M5/FG not claimed.

### 5.2 R2 — U5E signature corrected (actual namespace `Tools.ShippingGen2`)
`GenExtAtCall`, `SigAt`, `CallField`, `decA`, `decB`, `Pkg`, `Pkgs` live in `namespace Tools.ShippingGen2` (`T2Tie.lean:38/237`, `T2Dec.lean:29`); `Tools.ShippingGen5T2Tie.GenExtAtCall` does not exist.
The decoded families are `Tools.ShippingGen2.decA p q k hk` / `Tools.ShippingGen2.decB p q k hk` (bodies as in §0). Corrected statement (module `Tools/ShippingGen5SemExtPkg.lean`, imports `Tools.ShippingGen5SemExt`, `Tools.ShippingGen5T2Tie`, `Tools.ShippingGen5T2Range`, `Tools.ShippingGen5SemPkg`):
```lean
theorem genExtAtCall_of_genSem {ι : Type} {dom : ι → DomainConfig} (P : Tools.ShippingGen2.Pkgs ι dom) (X : Name) (g : GenIn)
    (p q : Tools.ShippingGen2.Pkg ι dom) (k : Nat) (hk : k < p.d.shape.insts.length)
    (hp : p.toSem = genSemI (semOf P) X g)
    (hq : P (p.d.shape.insts[k]'hk).1 = some q)
    (hord : (originOf p.d k).child? = none) :
    Tools.ShippingGen2.GenExtAtCall p q k hk
```
(`hnd` is removed from the statement; derived inside as in 5.1. `semOf`, `Pkg.toSem`, `genSemI` as at 783419ad in `Tools/ShippingGen5SemPkg.lean`/`SemGen`; the exact binder forms are re-read at that SHA when it is elaborated.)
**Scope of this issue run:** U5E is *type and dependency description only*; its elaboration is done after the U5A–D files are integrated. Nothing about U5E is claimed built.

### 5.3 R3 — Check: helper-type negative control
CLOSURE unknown controls (four now, plus the clean one), each run inside `withoutModifyingEnv`, the invalid fixtures added to the environment only there:
1. unknown **root** (name not in env) ⇒ `throwError`;
2. root itself forbidden-checked (a forbidden constant as the root is detected);
3. unknown **helper value**: root `R` (exists) whose *proof term* mentions an existing helper `H`, and `H`'s *value* mentions a missing constant `Mv`; the walker must throw and the thrown message must contain `Mv`;
4. unknown **helper type**: root `R` whose statement and proof reference an existing helper `H` only, where `H`'s **type** (not `R`'s type and not `H`'s value) mentions a missing constant `Mt`: path `R → H → type(H) ∋ Mt`; the check asserts it threw **and** that the message names `Mt` (the intended name) and not another;
5. **clean** control (same shape, no missing name) must pass.
The root statement itself never contains the unknown name in (3)/(4). Fixtures are built in-test with `Environment.addDecl` (axiom-free: the helper is a `defnDecl`/`thmDecl` with `sorry`-free bodies; the missing name is simply never declared) inside `withoutModifyingEnv`, so the library environment is not changed.
Counting rule stays: TYPE/DEFTYPE/DEFBODY/MUTANT/AXIOMS/CLOSURE/REACH are reported as real counts by category.
