# DG-READERTRACE freeze rev18（rev17 0dde7b2b の変更依頼への修正 + UserInlinerPh の証明見込み調査。文書のみ）

対象 Issue: `sparkle-gen5-dg-readertrace`。base: `kjob/rt22` 0dde7b2b（`DG_READERTRACE_FREEZE_REV17.md`）。
rev17 の §2.2（`CiFromEnv` と `shapeInputs_of` の `hci`）だけを置き換える。それ以外（§1 の `hrf` を `LiftAgrees` から導く方針、N1-a / N2-b / N3-b の完全型、N4-a、重複照合、D-b 先行、ptot-m4 の統合順）は rev16 / rev17 のまま変えない。
台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。Lean は編集していない。型はすべて未 elaborate。

## 0. rev17 への指摘と、rev18 の選択

reviewer の指摘（rev17、変更依頼）:

* `CiFromEnv` の inline 枝では `ci = inlinedConst (userInliner env) ci0`（`Elab.lean:3409`）。
* `DeclValuePh env`（rev15 §3.1）が与えるのは `ci0.value` の `NoPh` / `BvarLt 0` だけで、そこから `NoPh (userInliner env ci0.value) ∧ BvarLt 0 (userInliner env ci0.value)` は出ない。
* したがって rev17 §1.1 の完全型からは `hdecl` を作れない。

選択肢は (A) `UserInlinerPh` を条件として署名に足す（FG +1 候補）、(B) 非 inline 枝だけの条件付き定理に狭める。
**rev18 は (B) を採る。** 理由: `userInliner`（`Elab.lean:3387`）は Sparkle 自身のコードであり、ユーザー方針（2026-11-01: 自前のコードは仮定にせず全域化・証明する。仮定は停止が示せないものだけ）に照らすと、証明の見込みを調べる前に (A) の名前付き仮定を足すのは早い。見込みの調査は §3 に書く。

## 1. 置き換える完全型（非 inline 枝だけの条件付き定理）

```lean
/-- `ci` が `env` の定数そのもの（`entryConst` の `else ci` の腕）。rev16 の `hmem` と同じ形で、
    rev17 の `CiFromEnv` の左の選択肢だけ。 -/
def CiDirect (env : Lean.Environment) (ci : Lean.ConstantInfo) : Prop :=
  ∃ c : Lean.Name, env.find? c = some ci

theorem shapeInputs_of_direct (hz : ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : DeclValuePh env)
    (hci : CiDirect env ci)
    (hbr : PackTupleInputsBridge) (hraw : RawNodePh (structEnv env)) (hnode : NormNodePh (structEnv env))
    (hdom : …DomAtomic の節。D-b の結果が出るまで rev17 §1.1 のまま…)
    (hbs : ∀ p, shapePre sm ps ci (structEnv env) = some p → p.bs.length ≤ nDecl) :
    ShapeInputs nDecl (structEnv env) sm ps ci n
```

* `hdecl` の作り方: `hci` から `c` を取り、`ci = .defnInfo d`（`ci` が `defnInfo` でない場合は `ShapeInputs` が要求する値の読みが空なので rev16 §2 の場合分けのまま）なら `hv c d` が `NoPh d.value ∧ BvarLt 0 d.value` を与える。これは rev16 §2 の左の腕と同じ。
* `hrf` は rev17 §1.1 のとおり `Tools.PartialTotal.Agree.rootFloatAgrees hla` で導く（ptot-m4 を含む tree にだけ置く）。
* 名前を `shapeInputs_of_direct` にして、将来 inline 枝を含む `shapeInputs_of` を足すときに衝突させない。

**この定理が主張しないこと。** 実際の run で `entryConst` が `else ci` の腕を取ること（`entryConst`（`Elab.lean:5272`）は 4 つの条件のどれかで `inlinedConst inl ci` の腕を返す。その腕を取る run では `hci` は供給されない）。`hci` の供給元（`getConstInfo` の結果と `structEnv env` の `env` の同一性 = `GetEnvFrame` / 2 回の `getEnv` の同一性、rev17 §2.3 の (a)(b)）。これらは rev17 のまま未解消の義務。

## 2. inline 枝の `ShapeInputs` の供給（未解消）

* inline 枝（`ci = inlinedConst (userInliner env) ci0`）の `ShapeInputs` を、この調査は供給していない。署名にも載せない。
* inline 枝に必要な文は `NoPh (userInliner env ci0.value) ∧ BvarLt 0 (userInliner env ci0.value)`（以下 `UserInlinerPh`）。その供給元は §3 で調べる。**今回は 0/0 で、(A) の +1 は数えない。**
* `ci.type` 側（`inlinedConst` は `type := inl d.type` も書き換える）が `ShapeInputs` に要るかは、この調査では確かめていない（value の読みだけを確かめた）。

## 3. 調査: `UserInlinerPh` を定理として証明する見込み

形（証明したい文）: 任意の `env`、`DeclValuePh env` のもとで、`NoPh e ∧ BvarLt 0 e` なら `NoPh (userInliner env e) ∧ BvarLt 0 (userInliner env e)`（`e` が `ci0.value`）。実際には帰納のため `BvarLt L e → BvarLt L (…)` の形で一般化する。

### 3.1 `userInliner` の構成と、全域 / partial / extern の別

読んだ範囲（`Sparkle/Compiler/Elab.lean`、`MachRecUnfold.lean`、Lean v4.32.1 core）。「全域」は `partial` でも `extern` でも `opaque` でもない通常の `def`（構造再帰または fuel 再帰で kernel が受理している）の意味。

| 関数 | 場所 | 状態 | `NoPh` / `BvarLt` 保存の証明への影響 |
|---|---|---|---|
| `userInliner` | `Elab.lean:3387` | 全域（局所 `let rec rounds` は `Nat` の構造再帰） | 本体。下の部品に分けて証明する |
| `inlineDefs` | `Elab.lean:3202` | 全域（fuel と budget の構造再帰） | 証明できる見込み（下記） |
| `inlSpine` / `inlBeta` / `inlMap` | `3081` / `3072` / `3086` | 全域 | 同上 |
| `inlSubst` / `inlLift` | `3028` / `2987` | 全域（budget 再帰）。`Expr.instantiate` は使わず自前の置換 | 同上。**`Inst1Agrees` はここでは要らない**（rev18 指示の「代入には Inst1Agrees」は、`inlineDefs` 経路については当てはまらない。`Inst1Agrees` が絡むのは下の `headBeta` / `passM` 側） |
| `inlHeadCtor` | `3170` | 全域 | 同上 |
| `inlSignalApplicative` / `inlSignalMapOfFunctor` / `inlDropBinder` / `inlCanonLam` / `inlCanonPi` | `3150` / `3135` / `3100`（`inlCanonLam` 3122） | 全域 | 構造的。`inlDropBinder` は bvar を 1 下げるだけで `BvarLt` を保つ |
| `userDefinition?` | `3330` | 全域。`env.find? n = some (.defnInfo d)` のときだけ `some d.value` を返す | 返す値は env の定義の値そのもの → `DeclValuePh env` から `NoPh ∧ BvarLt 0` |
| `userProjection?` | `3349` | 全域 | 返すのは名前と数だけ（式を作らない） |
| `inlFoldNat` / `inlNatSum?` / `inlNatLit` / `canonicalNatLitValue?` | `3290` / `3270` / `3264` / `1389` | 全域 | リテラルと const だけを作る。構造的 |
| `isPrimitive` | `468` | 全域 | Bool 条件のみ |
| `inlAbbrevs` | `3376` | 全域（`Nat` 構造再帰）。ただし中で **`Expr.replace`**（`Lean/Util/ReplaceExpr.lean:16-19`、`@[extern "lean_replace_expr"] opaque`）と **`Expr.headBeta`**（→ `betaRev`、core で `partial`、`Lean/Expr.lean:1594`、内部で `instantiate` / `instantiateRange` の extern）を呼ぶ | **止まる点 S1**（§3.3） |
| `MachRecUnfold.pass` / `passM` | `MachRecUnfold.lean:276` / `243` | **`partial`**（kernel から見て opaque）。中で `iota`（62）、`reduceHead`（127）、`betaAll`（142）、`headBetaM`（54）、`listLit?`（172）も `partial`。`unfoldCall?`（155）は全域だが `Expr.beta`（`betaRev`）と `instantiateLevelParams` を呼ぶ | **止まる点 S2**（§3.3） |
| `MachRecUnfold.relevantClosure` | `283` | `partial` | **止まらない**: `userInliner` は `if relevantClosure … then A else B` で Bool としてしか使わない。`A` と `B` の両方で保存を証明すれば、`relevantClosure` の値に依らず結論が出る |
| `evalNode?`（`222`）/ `natVal?` / `boolVal?` / `mkListLit` / `natLitE` | `MachRecUnfold` | 全域（`evalNode?` はリテラルと const を作る。引数を返す腕があるかは未確認） | `passM` の中。S2 の一部 |
| `Expr.getUsedConstants` / `find?` / `==` | core | `==` は `Expr.eqv`（extern）だが、`if e' == e then … else …` の分岐でしか使わず、両腕とも保存を示せば値に依らない | 止まらない |

### 3.2 `NoPh` / `BvarLt` を保つ証明の筋道（止まる点 S1 / S2 を除く部分）

`userInliner env e` の形: `inlFoldNat (inlAbbrevs env 4 (rounds 64 e1))` または `inlFoldNat (inlAbbrevs env 4 e1)`、`e1 = inl e`、`inl e = (inlineDefs … e inlineDepth inlineBudget) の some なら e'、none なら e`。

1. **`inlineDefs` の保存補題**（新規ファイルの単位 P1）。`DeclValuePh env` の仮定下で、`inlineDefs (userDefinition? env) (userProjection? env) fuel e b = some (e', b')` かつ `NoPh e ∧ BvarLt L e` なら `NoPh e' ∧ BvarLt L e'`。`fuel` / `b` の帰納（定義の再帰と同形）。部品の補題:
   * `inlLift k c`: `BvarLt L e → BvarLt (L + k) (lift)`、`NoPh` は変えない。
   * `inlSubst xs d`: `xs` の各要素が `NoPh ∧ BvarLt L`、`e` が `BvarLt (L' ) …` のとき、結果は `NoPh ∧ BvarLt (…)`。置換される bvar は `xs` の要素を `d` 個の binder の下に `inlLift d 0` で持ち上げたもの、置換されない bvar は `i - xs.size` に下がる（`BvarLt` の境界が `xs.size` だけ下がることを使う）。
   * `inlBeta`: `lam` を剥がした数 = `acc.size` を `inlSubst` に渡す。
   * `defs n = some v` の腕: `v` は `DeclValuePh` により `NoPh ∧ BvarLt 0`、つまり閉じているので `inlBeta #[] v args` の結果は `BvarLt` が args の範囲に収まる。
   * projection の腕: `inlHeadCtor` の戻りは入力 record の部分項または `defs` の値の beta なので、同様に保存される（`inlHeadCtor` の P1 補題を別に起こす）。
   * `inlSignalApplicative`: `mkApp5 (.const …)` と引数の部分項のみ。`inlDropBinder` の保存は個別補題。
   * 不明な腕（`mdata` / `proj` が `inlSubst` で `none` になる）は `none` → `userInliner` は `e` 自身を返すので保存は自明。
2. **`rounds` の保存**: `Nat` の構造帰納。各ステップが `MachRecUnfold.pass`（S2）と `inl`（P1）の合成。
3. **`inlAbbrevs` の保存**（S1 を除く構造）: `userAbbrev? env c` が返す値は `env` の defnInfo の値で `¬ hasLooseBVars`（`BvarLt` の意味で閉じている）。`NoPh` は `DeclValuePh` から。置換は const → 閉じた値なので `BvarLt L` を保つ。`Nat` の構造帰納。
4. **`inlFoldNat` の保存**: `Expr` の構造帰納。`inlNatSum?` は const とリテラルのみを作る。
5. **合成**: `if relevantClosure … then A else B` を場合分け（`relevantClosure` の値は問わない）、`A`・`B` それぞれに 1〜4 を使う。

### 3.3 止まる点（この調査で見つかったもの）

* **S1: `inlAbbrevs` の `Expr.replace` と `headBeta`。** `Expr.replace` は `replaceImpl`（`opaque` + `@[extern "lean_replace_expr"]`）で、論理の中に内容がない。`Expr.headBeta` は `betaRev`（core の `partial`）→ `instantiate` / `instantiateRange`（extern）。したがって `inlAbbrevs` の保存は、(i) `replace f e = replaceNoCache f e` の一致、(ii) `headBeta` と `instantiate` 系の一致（`Inst1Agrees` は `instantiate1` だけ。`instantiate` / `instantiateRange` は別の文）を前提にしないと、論理の中で書けない。既存: `ZeroLitAgrees0`（T1L-54）は `zeroLit` 中の `Expr.replace` 用の同種の前提（`Tools/Assume/N3Extern.lean:25,67`）、`Inst1Agrees`（`Tools/ShippingLetsExternSpec.lean:121`）。`inlAbbrevs` 用の `replace` の一致が、既存の行の文に含まれているかは、この調査では照合していない（`ZeroLitAgrees0` は `zeroLitF` の置換について述べる文で、`abbrevFn` の置換には別途の文が要る）。既存の isolated candidate `Tools/ShippingInlCand.lean`（ヘッダに `replaceNoCache f e = replace f e` は OPEN と明記）は、`∀` 型の入力にだけ構造版を使う分解で、**値（`ci0.value`）の `replace` は扱っていない**。
* **S2: `MachRecUnfold.passM`（`partial`）。** kernel から見て opaque で、`NoPh` / `BvarLt` の保存を述べる定理を書いても証明項が作れない。中の `iota` / `reduceHead` / `betaAll` / `headBetaM` / `listLit?` も `partial`。`Tools/ShippingInlCand.lean` は `passF`（fuel 再帰）を用意しているが、同ファイルのヘッダのとおり `passF n e s = passM e s` は実行時の互換の議論であって kernel の等式ではない。par/ptot-m4 は同種の `partial` 3 定義（`machBoolMap` / `machLiftScalarN` / `rootFloat`）を fuel 化して `partial` を外した前例（共有定義 / compiler の変更。ユーザー承認が要る範囲）。`passM` を同じ方法で全域化すれば S2 は証明の単位に変えられる見込みがあるが、**それは compiler 定義の変更であり、rev18 の範囲ではない**（§4）。
* S1 / S2 のどちらも、`inlineDefs` 経路（P1）とは独立で、P1 は S1 / S2 に触れない。

### 3.4 証明できない部分だけが仮定の候補（domain つき）

次は候補であって、**今回は足さない・数えない**（0/0）:

* 候補 U-A（S2 を compiler 変更なしで局所化する場合）: `userInliner env` の `rounds` ステップの出力についての保存。`domain`: `env` が `DeclValuePh` を満たし、入力が `NoPh e ∧ BvarLt L e`、`MachRecUnfold.pass env canonicalNatLitValue? (isRec env) e` に対して `NoPh ∧ BvarLt L`。これは停止（`partial`）が示せないものに対する仮定で、`passM` の全域化（compiler 変更）が許されれば不要になる。
* 候補 U-B（S1）: `Expr.replace f e = Expr.replaceNoCache f e`（`f = abbrevFn env`、`e` は `NoPh ∧ BvarLt L`）と、`Expr.headBeta` の `instantiate` 系の一致。これは extern の一致で、既存の `ZeroLitAgrees0` / `Inst1Agrees` と同じ種類（C++ の extern）。**既存の行の文に含まれるかは未照合**。含まれなければ新規の T1 候補（件数は未計数）。
* どちらの候補も、`UserInlinerPh` そのものを仮定として足す (A) よりは狭い（保存の文ではなく、停止 / extern の一致のみ）。

### 3.5 結論

* **証明の単位を起こすべきか: はい（P1）。** `inlineDefs` / `inlSubst` / `inlLift` / `inlBeta` / `inlHeadCtor` / `inlSignalApplicative` / `inlFoldNat` / `rounds` の構造の保存補題は、全域な `def` だけで書け、新しい前提を要しないと見込む。ただしこれは見込みで、**未 elaborate・未証明**。
* **仮定 (A) `UserInlinerPh` が要るか: 要らない、と今は言える範囲ではない。** S1（`replace` / `headBeta` の extern）と S2（`passM` の `partial`）が残るため、`UserInlinerPh` 全体を無仮定で証明できるかは、S1 / S2 の扱いが決まるまで未定。この調査では S1 / S2 を越える経路は見つからなかった（導出不能の意味ではない）。
* **判断が要るか: 要る（ただし今回の rev18 では止めない）。** 次のいずれかはユーザー / reviewer の判断で、本 freeze では選ばない:
  1. S2 を `passM` の全域化（compiler 定義の変更、ptot-m4 と同じ方法）で解消する。
  2. S2 を U-A のような局所的な前提として足す（FG / T1 +1 候補。停止が示せないものだけを仮定にするという方針に合う形に限る）。
  3. 当面 inline 枝を未解消のまま、非 inline 枝の `shapeInputs_of_direct` で進める（rev18 の選択）。
  P1 の実装は、承認後の別 freeze で型を固定してから行う（本文書では型を freeze するのは §1 の `shapeInputs_of_direct` だけで、P1 は §3.2 の筋道の記述に留める）。

## 4. FG / T1 の差分

| 項目 | rev17 | rev18 |
|---|---|---|
| `hci` | `CiFromEnv`（2 腕、inline 枝は `hdecl` を作れない） | `CiDirect`（非 inline 枝のみ）。inline 枝は未解消と明記 |
| `UserInlinerPh` | 将来 +1 の候補 | **足さない**。§3 の調査で S1 / S2 が残るため、候補 U-A / U-B を挙げるにとどめる（未計数） |
| 候補 N1-a +1 / N2-b +1 / N3-b +2 | 未登録・未計数 | 同じ（N1〜N3 の +4 は候補のまま） |
| 今回の台帳差分 | 0/0 | **0/0**（FG 103 / T1 54） |

## 5. 主張しないこと

`hci` が供給されること、`GetEnvFrame` / `EnvSnapshot` が成り立つこと、2 回の `getEnv` の同一性、実際の run が非 inline 枝を取ること、inline 枝の `ShapeInputs`、`UserInlinerPh` の証明（見込みの調査のみ。未証明）、S1 / S2 を越える経路の存在 / 不存在、`ShapeInputs` の供給、C.RT-2 等の減算、N1-a / N2-b / N3-b の登録。「この調査では供給元・経路が見つからなかった」ものは導出不能の意味ではない。コンパイラ・共有定義・TRUSTED 境界・law は変えていない。`GenWF` は強化しない。mutant は使っていない（Lean なし）。

## 6. reviewer への依頼

1. §1 の `CiDirect` / `shapeInputs_of_direct` の型（非 inline 枝に狭めること、inline 枝を未解消として残すこと）。
2. §3.1 の全域 / partial / extern の読み（特に `relevantClosure` と `==` を Bool 分岐として扱って止まらないとする点、`inlineDefs` 経路は `Inst1Agrees` を要しないという訂正）。
3. §3.3〜3.5 の止まる点 S1 / S2 と、判断が要る点の整理（本 freeze では台帳に何も足さない）。
