# DG-READERTRACE freeze rev17（rev16 cf57a71d の変更依頼への修正。文書のみ）

対象 Issue: `sparkle-gen5-dg-readertrace`。base: `kjob/rt21` cf57a71d（`DG_READERTRACE_FREEZE_REV16.md`）。
rev16 の §6 と §2.2 だけを置き換える。それ以外（N1-a / N2-b / N3-b の完全型、N4-a、重複照合、D-b 先行）は rev16 のまま変えない。
台帳: FG 103 / T1 54（今回 FG -0 +0 / T1 -0 +0）。Lean は編集していない。

## 0. 読んだもの

`git show par/ptot-m4:Tools/PartialTotal/Agree.lean`（`rootFloatAgrees`）、`git show par/ptot-m4 --stat`（base d0ddc50b からの差分）、`git merge-tree HEAD par/ptot-m4`（衝突の確認のみ、ソースツリーではマージしていない）、`Sparkle/Compiler/Elab.lean`（`inlinedConst` 3409、`entryConst` 5272、`synthesizeFromConst` 5289〜5314、`getConstInfo` の呼び出し 5567）、`Tools/ShippingEnvRead.lean`（`getConstInfo_find`）、`Tools/ShippingEntryReadsLinked.lean`（`getConstInfo_value` 267、`ci_in_envR` 287）、`Tools/ShippingEnvSnapshot.lean`（`GetEnvFrame`、`ci_in_envR_of_frame`）、`Tools/ShippingCacheCoherentVia.lean`（`sfc_machine_val` 242）、`Tools/ShippingStRefCorrespondence.lean`（`getEnvFrame_of_readKeeps`）、FG 台帳 C.RK-2、T1 台帳 T1L-36。

## 1. 修正 1: `hrf : RootFloatAgrees` を `LiftAgrees` から導く

事実（`par/ptot-m4` 965fe51b、`Tools/PartialTotal/Agree.lean:106`）:

```lean
theorem rootFloatAgrees (hl : LiftAgrees) : RootFloatAgrees
```

`RootFloatAgrees`（T1L-52）は ptot-m4 で定理になり T1 台帳から除かれている（T1 54 は除いた後の値）。この base（kjob/rt21）はまだ ptot-m4 を含まず、`RootFloatAgrees` は `Tools/ShippingLetsExternSpec.lean:237` の仮説定義のまま。

### 1.1 `shapeInputs_of` の新しい署名（rev16 §6 を置換）

`hrf` の binder をやめ、`hla : LiftAgrees`（すでに引数にある）から導く。

```lean
theorem shapeInputs_of (hz : ZeroLitAgrees0) (hla : LiftAgrees) (hi1 : Inst1Agrees)
    (env : Lean.Environment) (hv : DeclValuePh env)
    (hci : CiFromEnv env ci)            -- §2。hmem の置換
    (hbr : PackTupleInputsBridge) (hraw : RawNodePh (structEnv env)) (hnode : NormNodePh (structEnv env))
    (hdom : …DomAtomic の節。D-b の結果が出るまで現行のまま…)
    (hbs : ∀ p, shapePre sm ps ci (structEnv env) = some p → p.bs.length ≤ nDecl) :
    ShapeInputs nDecl (structEnv env) sm ps ci n
```

本体の中で `shapeMid_ph hz (Tools.PartialTotal.Agree.rootFloatAgrees hla) …` と渡す。`shapeMid_ph`（U-R12c、179cbe7a）自体の署名 `(hrf : RootFloatAgrees)` は変えない（ptot-m4 統合の前後どちらの base でも同じ型なので、`shapeMid_ph` は再 build 不要）。

### 1.2 ptot-m4 の統合順（統合は coder。ソースツリーでは merge しない）

* ptot-m4（965fe51b）は base d0ddc50b から分岐しており、compiler の 3 定義（`machBoolMap`、`machLiftScalarN`、`rootFloat`、`Sparkle/Compiler/MachRawSurface.lean` と `Elab.lean`）の `partial` を外している。共有定義・compiler の変更を含むので、**最終統合・clean build の扱い**（共通ルール: 共有定義変更は clean build 対象）。
* `git merge-tree` による確認: 本 base（cf57a71d）と ptot-m4 の衝突は `lakefile.lean` の 1 ファイル（双方が `lean_lib` を末尾に追加した位置）だけ。解消は両側の `lean_lib` を残す（追加のみ）。他のファイルは自動マージされる。ただしこれは textual な確認で、build は未実行。
* 順序（推奨）: (1) ptot-m4 を、すでに下流統合済みの系列（par/gd-int2 など）に先に入れる、または (2) この base に ptot-m4 を merge（`lakefile.lean` の両側保持）し、`Tools.ShippingGen5ReaderTraceShapeIn` / `ReaderTraceShape` と ptot-m4 の `Tools.PartialTotal.Agree` を target build して整合を見る。どちらも **`shapeInputs_of` の実装より前**。`shapeInputs_of` は ptot-m4 を含む tree にだけ置く（`Tools.PartialTotal.Agree` を import するため）。
* ptot-m4 を含まない tree では `shapeInputs_of` は書けない。その場合の暫定形（`hrf : RootFloatAgrees` を残す）は **採らない**（T1 台帳の削除済み行を復活させる形になり、台帳差分が 0/0 でなくなる）。
* 台帳への影響: なし（T1L-52 は既に除かれた後の値 54 を使っている）。`LiftAgrees`（T1L-50）は既存の行のまま。

## 2. 修正 2: `hmem` の供給元

### 2.1 本番の呼び出しの読み（この調査で分かったこと）

`machineShape?` に渡る `ci` は `getConstInfo declName` の結果そのものではない。`Elab.lean:5567-5572`:

```
let constInfo ← getConstInfo declName
let env ← getEnv
synthesizeFromConst … (entryConst … constInfo (instancePredicate env) (userInliner env) (structEnv env)) …
```

`entryConst`（5272）は `ci` をそのまま返すか、`inlinedConst inl ci`（`Elab.lean:3409`: `.defnInfo { d with value := inl d.value, type := inl d.type }`）を返す。`synthesizeFromConst` はその結果を `constInfo` として受け、`machineShape? … constInfo (structEnv env)`（5314）を呼ぶ。

したがって rev16 の `hmem : ∃ c, env.find? c = some ci`（`ci` が `env` の定数そのもの）は、**`entryConst` が `inlinedConst` の腕を選んだ run では成り立たない**（`inlinedConst` の `value` は `inl d.value` で、`env` の `d.value` ではない）。rev16 の `hmem` の書き方は直す必要がある。

### 2.2 置換する型 `CiFromEnv`

```lean
def CiFromEnv (env : Lean.Environment) (ci : Lean.ConstantInfo) : Prop :=
  ∃ (c : Lean.Name) (ci0 : Lean.ConstantInfo),
    env.find? c = some ci0 ∧ (ci = ci0 ∨ ci = Sparkle.Compiler.Elab.inlinedConst inl ci0)
```

`inl` は `userInliner env`（`Elab.lean:3387`）に固定する（`CiFromEnv` は `env` と `ci` だけの関数にし、`inl := userInliner env` を定義の中で使う）。`entryConst` の `else ci` / `inlinedConst inl ci` の 2 腕に対応する。型は未 elaborate。

`DeclValuePh env` から `hdecl` を作る側:

* `ci = ci0` の腕: rev16 §2 の通り（`DeclValuePh env` から `NoPh ci0.value ∧ BvarLt 0 ci0.value`）。
* `ci = inlinedConst inl ci0` の腕: `NoPh (inl ci0.value) ∧ BvarLt 0 (inl ci0.value)` が要る。`userInliner env` が `NoPh` / `BvarLt 0` を保つ文（**`inl` の範囲保存**）は、この調査では**既存の補題も台帳の行も見つからなかった**。これは **未解消の義務**（下の §2.4）。

### 2.3 `ci0` が `env` の定数であることの供給（橋渡しとして証明できる部分）

既存の定理（読んだもの）:

| 定理 | 文 | 前提 |
|---|---|---|
| `Tools.ShippingEnvRead.getConstInfo_find` | `getConstInfo c` が `ci` を返す run があれば、**同じ world からの `getEnv` run の返す `env` について `env.find? c = some ci`** | なし（証明済み） |
| `Tools.ShippingEntryReadsLinked.getConstInfo_value` | `(envAt cref w).find? n = some ci`（`w` は `getConstInfo` の開始 world） | なし（証明済み） |
| `Tools.ShippingEntryReadsLinked.ci_in_envR` / `Tools.ShippingEnvSnapshot.ci_in_envR_of_frame` | `getConstInfo` の後の `getEnv` が返す `envR` についても `envR.find? n = some ci` | `EnvSnapshot`、または `GetEnvFrame`（EnvSnapshot:60、FG 台帳 C.RK-2 の EnvFrame、T1L-36 の側。`getEnvFrame_of_readKeeps` で `ReadKeeps` から導出可、`StRefCorrespondence:75`） |

* `getConstInfo declName` の結果 `ci0` と、`getEnv` が返す `env`（`synthesizeFromConst` の `machineShape?` が使う `structEnv env`、`Elab.lean:5313-5314`）は **別々の run**。同じ環境であることは `GetEnvFrame`（または `EnvSnapshot`）が要る。`ci_in_envR_of_frame`（証明済み）は、`GetEnvFrame` を仮定して `envR.find? n = some ci0` を出す。
* `ci_in_envR_of_frame` が使う `hget` / `henv` の run の順序は `doSynth`（5567-5572）の `getConstInfo` → `getEnv` と同じ形だが、`sfc_machine_val`（`Tools/ShippingCacheCoherentVia.lean:242`）が出す `envR` は **`synthesizeFromConst` 内の `getEnv`（5313）の結果**であり、`doSynth` の `getEnv`（5568）とは別の run。`doSynth` の `getConstInfo` から `synthesizeFromConst` 内の `getEnv` までの間の world の対応（`EntryReadsLinked` 側の連結）は、この調査では**接続された定理を見つけられなかった**。

結論（供給の経路）:

* 証明できる単位（新規ファイル、新しい前提なし、既存の定理の合成だけ）: `GetEnvFrame` を**既存の仮説のまま**仮定して、`getConstInfo` の run の後の `getEnv` が返す `envR` で `envR.find? declName = some ci0`。この補題は `ci_in_envR_of_frame` そのもので、**実質的に既存**。新しい単位として書くのは、`CiFromEnv envR (entryConst … ci0 …)` を出す小さな補題 `ciFromEnv_of_entryConst`（`entryConst` の 2 腕の場合分けだけ。`inlinedConst inl ci0` の腕は定義から `CiFromEnv` の右の選択肢が出る。証明可能と見込むが**未 elaborate**）。
* 残る義務（未解消）:
  * (a) `GetEnvFrame`（または `EnvSnapshot`）が実際の run で成り立つこと。既存の行 C.RK-2（`EnvFrame`）/ T1L-36 の側にあり、`ReadKeeps`（`StRefCorrespondence`）が形。**新しい行ではない**が、供給元は見つかっていない（「新しい runtime law は未承認」と T1L-36 の行にある）。
  * (b) `doSynth` と `synthesizeFromConst` の 2 つの `getEnv` が同じ環境であること、または `doSynth` が渡す `userInliner env` / `structEnv env`（5567 の `env`）と `synthesizeFromConst` 内の `env`（5313）の同一性。この調査では、これを繋ぐ定理を見つけられなかった。
  * (c) `userInliner env` が `NoPh ∧ BvarLt 0` を保つこと（§2.2 の `inlinedConst` の腕）。この調査では供給元・経路が見つからなかった。

### 2.4 台帳の数え方（`hmem` / `CiFromEnv` を定理の引数に置く場合）

* `CiFromEnv env ci` は **FG への入力として数えない・新しい台帳行にしない**。理由: (i) 左の腕 `ci = ci0 ∧ env.find? c = some ci0` は `getConstInfo_find` / `ci_in_envR_of_frame` で既存の定理から出る形で、その前提 `GetEnvFrame` は既存の行（C.RK-2 / T1L-36 の側）に属する、(ii) 右の腕は `entryConst` の定義の場合分け、(iii) `ShapeInputs` と同じく「呼び出し側が供給する名前付き入力」であり、新しい信頼境界の文ではない。
* ただし、これは **未解消の義務を消した扱いではない**。(a)(b)(c) が残る間、`shapeInputs_of` の `hci` は「供給されていない入力」で、`ShapeInputs` の実供給は主張しない。(c)（`inl` の範囲保存）は、供給元が見つからず、かつ `DeclValuePh` とは別の文なので、**将来これを FG に足すことになれば台帳の増加（+1）になる**。その場合は新しい行として別 freeze で reviewer に出し、数え直す。**今回は数えない（0/0）**。
* `hv : DeclValuePh env`（N1-a）は rev16 のまま FG +1 の見込み（未登録・未計数）。

## 3. FG / T1 の差分（rev17 で変わるもの）

| 項目 | rev16 | rev17 |
|---|---|---|
| `hrf : RootFloatAgrees` の binder | 残存（T1L-52 の復活になる） | 削除。`rootFloatAgrees hla` で導く。T1 差分 0 |
| `hmem` | `∃ c, env.find? c = some ci`（`inlinedConst` の腕で偽） | `CiFromEnv env ci`（2 腕）。行にしない。(a)(b)(c) を未解消義務として残す |
| 候補 N1-a +1 / N2-b +1 / N3-b +2 | 未登録・未計数 | 同じ（未登録・未計数） |
| 今回の台帳差分 | 0/0 | **0/0**（FG 103 / T1 54） |

RootFloat を直さずに T1L-52 相当を戻す場合は 0/0 でなくなるが、rev17 はそれを採らない（§1.2）。

## 4. 主張しないこと

`hci`（`CiFromEnv`）が供給されること、`GetEnvFrame` / `EnvSnapshot` が成り立つこと、`doSynth` と `synthesizeFromConst` の環境の同一性、`userInliner` の範囲保存、`ShapeInputs` の供給、C.RT-2 等の減算、ptot-m4 統合後の build の成功（`git merge-tree` は textual な確認だけ）、N1-a / N2-b / N3-b の登録。「この調査では供給元・経路が見つからなかった」ものは導出不能の意味ではない。型はすべて未 elaborate。コンパイラ・共有定義・TRUSTED 境界・law は変えていない。`GenWF` は強化しない。

## 5. reviewer への依頼

1. §1.1 の `hrf` の除去と、`ptot-m4` を含む tree にだけ `shapeInputs_of` を置く方針、§1.2 の統合順（coder が統合）。
2. §2.1 の読み（`machineShape?` の `ci` は `entryConst` を通るため `hmem` の rev16 の形は偽になりうる）と、`CiFromEnv` の 2 腕の型。
3. §2.4 の数え方（`CiFromEnv` を行にしない、(c) の `inl` の範囲保存は将来 +1 の候補で今回は 0/0）。
4. (a)(b)(c) を未解消の義務として残してよいか。
