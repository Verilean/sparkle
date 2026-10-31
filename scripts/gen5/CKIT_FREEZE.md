# CKIT freeze: 候補 C（C.AC-2 / C.AC-3 の除去、FG -2 +0）

agent `ckit1`、Issue sparkle-gen5-dg-kit、base `kjob/sm3-pa2` 4cade1d0。根拠: `git show 500c0370:scripts/gen2/PREMISE_LEDGER.md` §11.2 / §11.5（kjob/fgnext2）。
文書のみ。この freeze には Lean の実装（証明）を含まない。型は skeleton draft `Tools/ShippingGen5AccGenDataKit.lean`（sorry 本体、`kjob lake build Tools.ShippingGen5AccGenDataKit` で elaborate 確認済み、exit 0、5 つとも `declaration uses sorry` の警告のみ）に置いた。

## 1. 目標と消える ID

消える台帳 ID（2 行）: **C.AC-2**（`hev : GDEvidence …`）、**C.AC-3**（`hloc` / `hdecl` / `hd`）。
A（`Tools/ShippingGen5AccSemJoin.lean`）の carrier 固定 `GD := fun E => GenData dataOf E (structEnv env₀)`、`dOf := (·.d)`、`genSem := GenData.genSem hs`、`ordCallees := ordCallees₀` のもとで、`factsOf_genS_assembled'`（SM3、`Tools/ShippingGen5AccHinv.lean`）の 4 仮説 `hev hloc hdecl hd` を、既存の定理の適用 4 つに置き換える。

## 2. 新しい前提と仮説の判定表

**新しい前提: 0。**

| 仮説 | 台帳行 | 判定 |
|---|---|---|
| `hs : DataOfSound dataOf initsOf` | C.SM-1 | 残る（`genData_genSem_*` と `factsOf_genS_assembled''` が取る） |
| `genData₀` | carrier | 関数引数（成功は C.AC-4 / C.SM-6 側。台帳の前提に数えない） |
| `hev` | C.AC-2 | 消える（`genData_gdEvidence`。`hs` も取らない） |
| `hloc` `hdecl` `hd` | C.AC-3 | 消える（`genData_genSem_local` / `_decl` / `_d`） |

## 3. 純差分

消える 2（C.AC-2、C.AC-3）− 新しい前提 0 = **FG -2 +0 / T1 -0 +0**。移し替えではない（別の未供給境界に帰着せず、既存の定理で直接出る見込み。ただし証明は未実装で、その見込みは供給の主張ではない）。計上は freeze 承認と本番 proof-accept 合格後。現在値 FG 107 / T1 58。

## 4. 完全な型（`Tools/ShippingGen5AccGenDataKit.lean`、namespace `Tools.ShippingGen5Acc`、`import Tools.ShippingGen5AccHinv`、body は sorry）

共通: `variable {ι : Type} {dom : ι → Sparkle.Core.Domain.DomainConfig} {env₀ : Environment}`、`open Lean Meta Sparkle.Compiler.Elab Tools.ShippingGen2 Tools.ShippingGen5Sem`、`open Tools.ShippingMachineAuto (MachineData)`、`open Sparkle.Core Sparkle.Core.Domain Sparkle.Core.Signal Sparkle.IR.Machine Sparkle.IR.Semantics`、`open Tools.ShippingMachineDenote Tools.ShippingMachineSource`（SM3 の AccHinv と同じ）。

```lean
theorem genData_gdEvidence
    (dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData) :
    GDEvidence dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) env₀

theorem genData_genSem_decl
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).decl = X

theorem genData_genSem_d
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    ∀ (Q : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (GenData.genSem hs Q X g).d = g.d

theorem genData_genSem_local
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)} (hs : DataOfSound dataOf initsOf) :
    ∀ (Q Q' : Name → Option (SemPkg ι dom)) (X : Name) {E : ConstantInfo} (g : GenData dataOf E (structEnv env₀)),
      (∀ k ∈ ordCallees₀ g.d, Q (g.d.shape.insts[k]).1 = Q' (g.d.shape.insts[k]).1) →
      GenData.genSem hs Q X g = GenData.genSem hs Q' X g

theorem factsOf_genS_assembled''
    {dataOf : ConstantInfo → StructEnv → MachineShape → Option MachineData}
    {initsOf : (d : MachineData) → HList (tys d.ss)}
    (hs : DataOfSound dataOf initsOf)
    (genData₀ : (E : ConstantInfo) → Option (GenData dataOf E (structEnv env₀))) :
    ∀ (X : Name) (s : SemPkg ι dom),
      genS (mkKit dataOf (fun E => GenData dataOf E (structEnv env₀)) (fun {E} g => g.d) genData₀ ordCallees₀
        (fun Q X {E} g => GenData.genSem hs Q X g) ordCallees₀_mem
        (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)) X = some s →
      FactsOf s
```

`factsOf_genS_assembled''` の仮説は `hs` と carrier `genData₀` だけ。`factsOf_genS_assembled'` との差は `hev hloc hdecl hd` の 4 binder が上の 4 定理の適用に置き換わることだけ。

証明の案（案であって freeze の対象ではない。実装の最初の作業で確かめる）:
- `genData_gdEvidence`: `fun E g => genData_evidence (structEnv env₀) E g`
- `_decl`: `genSemI_decl Q X (g.toIn hs)`（`GenData.genSem hs Q X g = genSemI Q X (g.toIn hs)` の展開）
- `_d`: `genSemI_d Q X (g.toIn hs)` と `genData_toIn_d`
- `_local`: `genSemI_local Q Q' X (g.toIn hs)`、前件を `ordCallees_eq_ordCallees₀`（A、`Tools/ShippingGen5AccSemJoin.lean:27`）で書き換える
- `factsOf_genS_assembled''`: `factsOf_genS_assembled' hs genData₀ (genData_gdEvidence dataOf) (genData_genSem_local hs) (genData_genSem_decl hs) (genData_genSem_d hs)`

## 5. 前提条件（明記）

1. **A の carrier 固定（GenData-kit）を最終 assembly が採ることが前提。** A13 の `GDf` / `genDataF`（`GenData` と別型、DG_ACC freeze 承認済み・Lean 未実装）を最終 assembly の kit に採る場合は、C.AC-2 / C.AC-3 が別の `GD` について再び要る（その場合この freeze の減算は成立しない）。A 自体がこの carrier を前提にしている（CANDA_FREEZE §3）ので新しい決定ではないが、「A を承認 = GenData-kit を採る」を C の前提として明記する。
2. 本番 proof-accept が通っていること: A（628bc5d3、`ordCallees_eq_ordCallees₀`）、SM3（4cade1d0、`factsOf_genS_assembled'`。C は SM3 の上に積む）。

## 6. 減算に入れない行

C.AC-4（`ReachCover`、`genData₀` の成功）、C.AC-5、C.AC-7、C.AC-9（`RunDataLink` を含む）、C.SM-6（`GenWF`）、A.P-24（C.AC-8 統合）。いずれもこの freeze は消さないし、供給元もこの調査では辿れていない（「供給元・経路が見つからなかった」の意味で、不可能の意味ではない）。C.SM-1 も残る（候補 D は別単位）。

## 7. mutant 案（Check 用。signature / defeq での棄却であって意味的反例ではない）

`Tests/Gen5/CKitCheck.lean`（案、新規）で、`ExpectedType` で 5 定理の型を固定し、次を `example` の型不一致 / defeq 判定の失敗として棄却する:
- `genData_gdEvidence` の `dOf` を `fun {E} g => g.d` から別の関数に変えた型。
- `_decl` の結論を `= X` から別の名前に変えた型、`_d` の結論 `= g.d` を別の `MachineData` に変えた型。
- `_local` の前件の `ordCallees₀ g.d` を別のリストにした型、結論の `Q'` を `Q` にした型。
- `factsOf_genS_assembled''` に余分な仮説を足した型、または `hs` を落とした型。
- HYP の表: `factsOf_genS_assembled''` の binder が `hs genData₀` のみであること。
これらは型の字面 / defeq の棄却であり、意味的な反例の構成ではない。

## 8. 主張しないこと

- 供給（`DataOfSound`、`genData₀` の成功、`GenWF`、実 run）、共同充足性、FG の証明、DG-ACC / M5 の完了は主張しない。
- 新しい TRUSTED 境界・law・FG/保証の変更・FG の縮小・GenWF の強化はない。共有定義（Tools/ShippingGen2Defs.lean、T1Hyp、T1HypND、Elab*.lean）は編集しない。
- 新規ファイルは `Tools/ShippingGen5AccGenDataKit.lean`（と Check）のみ。lakefile.lean は lean_lib の追加のみ。
- 5 定理の証明は freeze 承認後の proof-accept（manifest 付き）で受理する。この freeze の時点では sorry 本体である。
