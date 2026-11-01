# SM3 FREEZE: C.SM-3 (`hinv`) を候補 A の組み立てから消す (純差分 -1 / 追加 0)

対象: kjob/smb1、base 9550d834 (候補 A candidate)。**文書のみ。Lean は承認後。** 台帳前提の除去なので reviewer 承認が要る。

## 1. 調査結果
`factsOf_genS_assembled`（Tools/ShippingGen5AccSemJoin.lean）の仮説 `hinv`（C.SM-3）の結論は、固定 carrier
（`GenData` / `structEnv env₀` / `ordCallees₀` / `mkKit`）で既存の 2 定理から出る:
- `genS_some_inv`（Tools/ShippingGen5Acc.lean:143）: `genS K X = some s` から `∃ E g, entry₀ env₀ X = some E ∧ K.genData₀ E = some g ∧ Acc (CallRel K) X ∧ … ∧ s = K.genSem (genS K) X g`。
  `Acc` と `s = genSem …` の 2 連言がそのまま `hinv` の 1 番目・3 番目の連言。
- `callEdge_of_ord`（同:79）: `entry₀ … = some E`、`genData₀ E = some g` から `∀ k ∈ K.ordCallees (K.dOf g), CallEdge K X (insts[k]).1`。`CallRel K c X = CallEdge K X c`（flip）なので `hinv` の 2 番目の連言。
- `K = mkKit …` の射影 `GD`/`dOf`/`ordCallees`/`genSem` は defeq で `GenData`/`g.d`/`ordCallees₀`/`GenData.genSem hs` に簡約される。
新しい前提は要らなかった。この調査では、`hinv` の供給元として他の台帳行に頼る経路は不要だった（hev/hloc/hdecl/hd は既に `mkKit` の引数で、`hinv` と無関係に既存の行 C.AC-2/C.AC-3）。

## 2. 完全な型（新規ファイル Tools/ShippingGen5AccHinv.lean、namespace Tools.ShippingGen5Acc、`import Tools.ShippingGen5AccSemJoin`）
下の 2 つの**型**は、この作業ツリーで body つき（Acc/CallEdge 補題による証明）で elaborate し `kjob lake build Tools.ShippingGen5AccHinv` が exit 0（742 jobs、sorry/axiom なし）で通ることを確かめた。確認用ファイルはコミットしていない（承認前に Lean を入れない）。以下の `sorry` は freeze 文書上の本体の省略表記で、実装は承認後。

```lean
theorem hinv_genS
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
      (GenData.genSem hs Q X g).d = g.d) :
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s →
      ∃ (E : ConstantInfo) (gd : GenData dataOf E (structEnv env₀)),
        Acc (CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X ∧
        (∀ k ∈ ordCallees₀ gd.d, CallRel (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) ((gd.d.shape.insts[k]).1) X) ∧
        s = GenData.genSem hs (genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
          (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd)) X gd := by
  sorry

theorem factsOf_genS_assembled'
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
      (GenData.genSem hs Q X g).d = g.d) :
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem hev hloc hdecl hd) X = some s → FactsOf s :=
  factsOf_genS_assembled hs genData₀ hev hloc hdecl hd (hinv_genS hs genData₀ hev hloc hdecl hd)
```
（`factsOf_genS_assembled'` の本体は既存 `factsOf_genS_assembled hs genData₀ hev hloc hdecl hd (hinv_genS hs genData₀ hev hloc hdecl hd)`。）

## 3. 仮説の判定表（`factsOf_genS_assembled'`）
| 仮説 | 台帳 | 判定 |
|---|---|---|
| hs : DataOfSound | C.SM-1 | 変更なし（残る） |
| genData₀ | 関数引数（成功は C.AC-4 側） | 変更なし |
| hev : GDEvidence | C.AC-2 | 変更なし（残る） |
| hloc / hdecl / hd | C.AC-3 | 変更なし（残る） |
| ~~hinv~~ | **C.SM-3** | **消える**（`hinv_genS`） |

## 4. 台帳の差分
- 消える ID: **C.SM-3**（`hinv`。`hunf` は `hunf_of_genData` 経由で `hinv` から出ているので、候補 A の組み立ての範囲では `hunf` 側も不要）。
- 増える前提: **0**。
- **純差分 -1 / 追加 0**。台帳: FG 107 / T1 58（今回 FG -1 +0 / T1 -0 +0）。
- 範囲の注意: carrier は `GenData`/`structEnv env₀`/`ordCallees₀`/`mkKit` に限る。`DataOfSound`、`genData₀` の成功、`GenWF`、実 run、C.AC-8/A.P-24 は供給しない。C.SM-3 の行が他の carrier を持つ場合は消えない（候補 A の組み立てから消える、という意味）。

## 5. 次
reviewer 承認後、新規ファイルに実装し、manifest 付き proof-accept（coder が manifest を作る）。mutant は signature/defeq での棄却であって意味的反例ではない。
