# 候補 A 流れ freeze: C.SM-4 と C.SM-2 を消す（純差分 +2 / 追加 0）

agent `canda1`、branch `kjob/canda1`、base `kjob/candA-int` 6a167f19（g5sm-u23 7af6c7cc + g5ac 7e3991af ⊇ cff12a48、lakefile は和集合）。
Issue `sparkle-gen5-dg-sem`。**文書のみ。コミットする Lean はない。** 根拠は `git show b54e343d:scripts/gen2/PREMISE_LEDGER.md` §10.1 / §10.3。

これは reviewer 承認が要る流れ freeze（台帳前提の消去・付け替え、carrier の固定を含む）。承認前に Lean 実装へ進まない。
「消えた」とは言わない。実装・Check・clean build・最終受理の後に台帳へ反映する。conditional な部品であり、供給・共同充足性・FG 証明は主張しない。

## 1. 目標と台帳差分

- 消える台帳 ID（2 行）: **C.SM-4**（`hacc`）、**C.SM-2**（`hmem`、`ordC := ordCallees₀` に限る）。
- 新しい前提: **0**。使う仮説はすべて既存行（§3）。
- **純差分 +2 / 追加 0。** 現在値 FG 107 / T1 58。この freeze の時点の前提差分は 解消 0 / 追加 0（承認・実装・build 後に FG 105 となる見込み。追加が出たら止めて coder に報告）。
- 減算に入れない: C.AC-8、A.P-24（§5）。`hacc_of_top_runs` は使わない。

## 2. 完全な Lean 型（この統合木 6a167f19 で elaborate 済み）

確認方法: 統合木で、新規の使い捨てファイル（`import Tools.ShippingGen5AccOrdCallees` と `import Tools.ShippingGen5SemGenData`）に下の 3 定理を**証明つきで**置き、
`kjob lake build` を実行した。結果は exit 0、741 jobs、エラーなし。3 定理（と §6 の観察用の `hinv_genS`）の `#print axioms` は `propext, Classical.choice, Quot.sound` のみ。
使い捨てファイルと、その lean_lib を足した lakefile は削除済みで、コミットには含まない。コードの確認であって、Check（TYPE/MUTANT/CLOSURE）はまだ書いていない。

共通の準備（新ファイルの冒頭。名前空間は `Tools.ShippingGen5Acc`、実装時のファイル名の案は §7）:

```lean
namespace Tools.ShippingGen5Acc
open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem
open Tools.ShippingMachineAuto (MachineData)
open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine Sparkle.IR.Semantics
open Tools.ShippingMachineDenote Tools.ShippingMachineSource
variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}
```

### 2.1 `hacc_genS`（A1 `genS_some_inv` の系。C.SM-4 の消去）

```lean
theorem hacc_genS (K : AssignKit ι dom env₀) :
    ∀ (Y : Name) (s : SemPkg ι dom), genS K Y = some s → Acc (CallRel K) Y
```
証明（elaborate 済み）: `obtain ⟨_, _, _, _, hacc, _, _⟩ := genS_some_inv K hs; exact hacc`。

### 2.2 `ordCallees_eq_ordCallees₀`（SEM の `ordCallees` と ACC の `ordCallees₀` を結ぶ）

```lean
theorem ordCallees_eq_ordCallees₀ (d : MachineData) : ordCallees d = ordCallees₀ d
```
`ordCallees` は `Tools.ShippingGen5Sem.ordCallees`（`Tools/ShippingGen5SemCall.lean:17`）、`ordCallees₀` は `Tools/ShippingGen5AccOrdCallees.lean:17`。
証明（elaborate 済み）: `unfold ordCallees ordCallees₀; apply List.filter_congr; intro k _; cases ((d.shape.instOrigins.getD k .ord).child?) <;> simp`。
**注:** C.SM-2 の `hmem`（`k ∈ ordC d ↔ … .child? = none`）自体は `ordCallees₀_mem` が直接満たす。この等式は `ordCallees₀` と SEM の `ordCallees`（`hunf` の `∀ k ∈ ordCallees g.d`）を結ぶ橋で、`hloc` を SEM の局所性補題 `genSemI_local`（`ordCallees g.d` で述べる）につなぐ実装段階で使う。組み立て（§2.3）の型には現れない。

### 2.3 組み立て: `hacc` と `hmem` に `G := genS K`、`R := CallRel K`、`ordC := ordCallees₀` を渡した結論

K は `mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀ (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd`。
読みやすさのため、型は `K` に束ねず原文で展開する（elaborate した形のまま）。

```lean
theorem factsOf_genS_assembled
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀)))
    (hev : GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀)
    (hloc : ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g)
    (hdecl : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X)
    (hd : ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d)
    (hinv : ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X gd) :
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s → FactsOf s
```
証明（elaborate 済み）:
```lean
  factsOf_all_of_acc_unfold _ _
    (hunf_of_genData hs (structEnv env₀) ordCallees₀ ordCallees₀_mem _ _ hinv)
    (hacc_genS _)
```
読み方: `factsOf_all_of_acc_unfold` の `hacc` 引数に `hacc_genS`、`hunf_of_genData`（→ `hunf_of_kitInv`）の `hmem` 引数に `ordCallees₀_mem` を渡している。`hsem` と `hd`（toIn 側）は `GD := GenData` のとき
SemGenData の `genData_genSem_eq_via` / `genData_toIn_d`（どちらも `rfl`）が埋めるので、新しい仮説は出ない。

## 3. 仮説の判定表（組み立て §2.3 の仮説 1 つずつ）

| 仮説 | 判定 | 台帳行 / 根拠 |
|---|---|---|
| `hs : DataOfSound dataOf initsOf` | **既存行 C.SM-1**（merged C.DO-1, C.AC-1） | `Tools/ShippingGen5SemGenData.lean:18` |
| `hev : GDEvidence …` | **既存行 C.AC-2** | `Tools/ShippingGen5AccGenDataEv.lean:22`。`GD := GenData` の `genData_evidence`（`hshape`/`hdata`）で埋まる形だが、この freeze は C.AC-2 を消さない |
| `hloc` / `hdecl` / `hd` | **既存行 C.AC-3** | 型は `mkKit` の引数。`GenData.genSem hs` に具体化した形 |
| `hinv` | **既存行 C.SM-3**（`hinv`/`hunf`）。SEM の `factsOf_all_of_kitInv` の `hinv` と同形で `G := genS K`、`R := CallRel K`、`ordC := ordCallees₀`、`genSemK := GenData.genSem hs` | `Tools/ShippingGen5SemKitInv.lean:58`。**C.SM-3 は本 freeze では消さない**（§6 の観察を参照） |
| `genData₀` | carrier（データ。仮説ではない）。`GenWF`/成功は C.SM-6 / C.AC-4 の側 | `AssignKit.genData₀`（`Tools/ShippingGen5Acc.lean:36`） |
| `dataOf`、`initsOf`、`env₀`、`ι`、`dom` | carrier（binder） | — |
| `hsem`、`toIn` 側の `hd` | 前提ではない（`GD := GenData` では `rfl` 定理 `genData_genSem_eq_via` / `genData_toIn_d`） | `Tools/ShippingGen5SemGenData.lean:46-55` |

**新しい前提: 0。** 消える行: C.SM-4（`hacc`、`hacc_genS` が供給）、C.SM-2（`hmem`、`ordCallees₀_mem` が供給。`ordC := ordCallees₀` に限る）。
`hacc_genS` と `ordCallees₀_mem` は仮説なしの定理（`genS_some_inv` は `K` と `hs : genS K X = some s` だけを取る）。

**reviewer 確認事項（carrier の固定・付け替え）:**
1. 組み立ては `K` を `mkKit … GD := fun E => GenData dataOf E (structEnv env₀) … ordCallees₀ …` に固定する。これは §8.4 の「DG-SEM と DG-ACC を 1 本の木に置く（kit K の carrier を固定）」の決定であり、
   C.SM-2 / C.SM-3 / C.SM-4 / C.AC-3 / C.AC-5 の行の `K` / `Reach` carrier の固定になる。台帳前提の付け替えに当たるので承認を求める。
2. A13（`GDf` / `genDataF`）の `GD` は `GenData` と別の型で、`GDf` には `GenWF` がない。組み立ては `GenData` を使い、`genData₀` は binder のまま（A13 の `genDataF` は使わない）。`GenWF`（C.SM-6）と `genData₀` の成功（C.AC-4）は未供給のまま。
3. 5 つの carrier（`dataOf`、`GD`、`dOf`、`genData₀`、`genSem`）を前提に数えるかは §8.3 の規則（数えない）のまま。数えると決めるなら本 freeze の +2 が変わる。

## 4. 前提確認: SEM 側の `hacc` / `hmem` の実際の署名（原文）

`hacc`（`Tools/ShippingGen5SemAccStep.lean:36-40`、branch g5sm-u23@7af6c7cc、統合木 6a167f19 で確認）:
```lean
theorem factsOf_all_of_acc_unfold (R : Name → Name → Prop) (G : Name → Option (SemPkg ι dom))
    (hunf : ∀ (Y : Name) (s : SemPkg ι dom), Acc R Y → G Y = some s →
      ∃ g : GenIn, s = genSemI G Y g ∧ ∀ k ∈ ordCallees g.d, R ((g.d.shape.insts[k]).1) Y)
    (hacc : ∀ (Y : Name) (s : SemPkg ι dom), G Y = some s → Acc R Y) :
    ∀ (X : Name) (s : SemPkg ι dom), G X = some s → FactsOf s
```
`hmem`（`Tools/ShippingGen5SemKitInv.lean:18-19` / `34-35` / `58-59` / `Tools/ShippingGen5SemGenData.lean:65-66` で同形）:
```lean
(hmem : ∀ (d : MachineData) (k : Fin d.shape.insts.length),
  k ∈ ordC d ↔ (d.shape.instOrigins.getD k .ord).child? = none)
```
一致の確認: `hacc` は `hacc_genS K` の型（`G := genS K`、`R := CallRel K`）と**字面まで一致**する。`hmem` は `ordCallees₀_mem`（`Tools/ShippingGen5AccOrdCallees.lean:21`）の型 `k ∈ ordCallees₀ d ↔ (d.shape.instOrigins.getD k .ord).child? = none` と
`ordC := ordCallees₀` で一致する（§2.3 は両方をこの形で渡して elaborate 済み）。台帳 §10.1 が懸念した `ordCallees`（述語 filter）と `ordCallees₀`（`isNone`）の字面の違いは `hmem` の型には現れず、`hunf` の側（`∀ k ∈ ordCallees g.d`）にだけ現れる。そのため `ordCallees_eq_ordCallees₀`（§2.2）を置く。
なお SEM の `factsOf_all_of_kitInv` / `factsOf_all_of_genDataInv` に `hacc` の binder はなく、`Acc` は `hinv` の連言の中にある。`hacc` の binder は `factsOf_all_of_acc_unfold` だけなので、§2.3 はそちらを使って `hunf` を `hunf_of_genData` から作る。

## 5. 注記

- **`hacc_of_top_runs` は使わない。** C.SM-4 の消去に run は不要（`genS_some_inv` が `Acc` を返す）。
- **C.AC-8 と A.P-24 は減算に入れない。** A.P-24 を FG の数に残すかは別の reviewer 確認事項のまま。
- Check を実装後に書く場合の mutant は signature / defeq での棄却であって、意味的反例ではない。
- 供給（実 `dataOf` / `DataOfSound` / `genData₀` / `GenWF`）、共同充足性、run、M5、FG の証明は主張しない。「この調査では供給元・経路が見つからなかった」ものは未供給のまま。

## 6. 観察（本 freeze の範囲外、台帳には数えない）

統合木で `hinv_genS` も elaborate した（証明は `genS_some_inv` と `callEdge_of_ord`、axioms は標準 3 つのみ）:
```lean
theorem hinv_genS (K : AssignKit ι dom env₀) :
    ∀ (X : Name) (s : SemPkg ι dom), genS K X = some s →
      ∃ (E : ConstantInfo) (gd : K.GD E), Acc (CallRel K) X ∧
        (∀ k ∈ K.ordCallees (K.dOf gd), CallRel K (((K.dOf gd).shape.insts[k]).1) X) ∧ s = K.genSem (genS K) X gd
```
これは §2.3 の `hinv` と同形の結論で、つまり kit 由来の `genS` については C.SM-3 の `hinv` も A1 と `callEdge_of_ord` から出る見込みがある（`mkKit` の K に当てはめる際の `K.ordCallees = ordCallees₀`、`K.genSem` の展開は defeq）。
**この freeze はそれを採らない**（+2 の範囲を超える。C.SM-3 の `hunf` と `hinv` の関係、`GenData` carrier での定理化、別の台帳付け替えが要る）。採るかは reviewer / coder の判断で、採るなら別の単位として freeze を起こす。純差分を +3 と書くのは、その単位が承認・実装されてからにする。

## 7. 実装計画（承認後。Lean はまだ書かない）

- 新規ファイル（案）: `Tools/ShippingGen5AccSemJoin.lean`（§2 の 3 定理）と `Tests/Gen5/AccSemJoinCheck.lean`（TYPE: 独立に書いた期待型との比較、MUTANT: signature/defeq 棄却、AXIOMS: 標準 3 つ、CLOSURE）。lakefile.lean に lean_lib を追加（可）。共有定義・コンパイラ・T1Hyp 等は編集しない。
- 新しい law / TRUSTED 境界 / sorry / axiom / native_decide はなし。
- 実装後は doing のまま coder に build を任せる。
