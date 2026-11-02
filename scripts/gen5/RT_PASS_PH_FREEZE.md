# RT pass_ph freeze（`sparkle-rt-pass-ph`、親 `sparkle-gen5-dg-readertrace`）

対象 Issue: `sparkle-rt-pass-ph`。base: `par/rt-pass-ph` 73e78c8f。rev1。
この文書は、台帳前提の追加候補（T1 +1 候補、RecRulePhU の扱い）と、旧 `PassPh` の型の置き換えを含む freeze なので reviewer の承認が要る。承認が出るまで Lean 実装には進まない。Lean ソースは何もコミットしていない（scratch のみ、§1。scratch は build 後に破棄した）。

結果の位置づけ: 条件付き・中間結果。`pass_ph` はまだ証明していない。ここに書くのは型と、証明の分解・必要な仮定だけ。coder の判断（案 A、2026-11-01 の既存方針: 不透明な C++ の振る舞いは Tools/Assume の小さな明示の仮定にして、合成の法則はそこから証明する）に従う。新しいユーザー判断は要らない。

## 0. 要約

* 旧 `PassPh`（0e16378b）は仮説だったが、新しい `pass_ph` は **定理** として、次の仮定の下で証明する: `DeclValuePh`（N1-a、既存）、`RecRulePhU`（承認済み freeze bab003d9 の文、仮説のみ）、`ReplaceAgrees`（U-1）、`Inst1Agrees`（T1L-51、既存）、`HeadBetaAgrees0`（U-2）、**新しい `BetaNonTargetAgrees`（T1 の新しい候補 1 件）**。
* 既存の `HeadBetaAgrees0` で足りるか: **`unfoldCall?` の `v.beta args` の一部は足りない**（§2）。`headBetaM` の `f.beta args`（`f` はラムダ）は `HeadBetaAgrees0` で足りる見込み（§2.2、導出補題は未証明）。足りない残りだけを最小の形（`isHeadBetaTargetFn = false` の頭に限る）で新しい仮定にする。
* 数: T1 の新しい候補 +1（相殺しない）。FG の変化 0。旧 `PassPh`（U-3 候補、未登録）は受理で不要になる（§5）。

## 1. (a) `PassPh'` の完全型（scratch で elaborate、`set_option autoImplicit false`）

`pass` は `Except String Expr` を返す（2df5d4d7）。燃料切れは `.error`（沈黙して切らない）なので、`.ok r` のときだけ `r` が `NoPh ∧ BvarLt 0`、`.error` は空虚に成り立つ。`natLit?` は 0e16378b では `canonicalNatLitValue?` に固定だったが、`natLit?` は `natLitE`（閉じた `NoPh` の項）を作る側でしか値を使わないので、任意の `natLit?` について証明する（`canonicalNatLitValue?` への特殊化は 1 行）。

```lean
/-- (hypothesis only; approved freeze RT_RECRULE_FREEZE §1.2, bab003d9。0e16378b:Tools/ShippingGen5ReaderTraceInlineCompose.lean と同じ文) -/
def RecRulePhU (env : Lean.Environment) : Prop :=
  ∀ (p : Lean.Name) (rv : Lean.RecursorVal) (c : Lean.Name) (r : Lean.RecursorRule),
    env.find? (.str p "rec") = some (.recInfo rv) → rv.rules.find? (·.ctor == c) = some r →
    NoPh r.rhs = true ∧ BvarLt 0 r.rhs = true

/-- (NEW T1 候補、Tools/Assume/ に置く、§2.3) `Expr.beta` が `headBeta` の対象でない頭に対して `mkAppN` と一致する -/
def BetaNonTargetAgrees : Prop :=
  ∀ (f : Lean.Expr) (args : Array Lean.Expr), f.isHeadBetaTargetFn false = false → f.beta args = mkAppN f args

theorem pass_ph (natLit? : Lean.Expr → Option Nat) :
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgrees0 → BetaNonTargetAgrees →
    ∀ (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true

theorem passWith_ph (natLit? : Lean.Expr → Option Nat) :   -- 同じ仮定。燃料を一般にした形（pass_ph の補題）
    ∀ (env : Lean.Environment), Tools.Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env →
    ReplaceAgrees → Inst1Agrees → HeadBetaAgrees0 → BetaNonTargetAgrees →
    ∀ (fuel : Nat) (isUser : Lean.Name → Bool) (e r : Lean.Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.passWith fuel env natLit? isUser e = .ok r →
      NoPh r = true ∧ BvarLt 0 r = true
```

scratch の `#check` 出力（`kjob lake build Tools.ScratchPassPh`、exit 0、本体は `sorry` で型だけ。実装ファイルには sorry を残さない）:

```
BetaNonTargetAgrees : Prop
beta_target : ∀ (f : Expr) (args : Array Expr),
  Expr.isHeadBetaTargetFn false f = true → ¬f.isApp = true → f.beta args = (mkAppN f args).headBeta
pass_ph : ∀ (natLit? : Expr → Option Nat) (env : Environment),
  Assume.EnvDeclValue.DeclValuePh env → RecRulePhU env → ReplaceAgrees → Inst1Agrees → HeadBetaAgrees0 →
    BetaNonTargetAgrees → ∀ (isUser : Name → Bool) (e r : Expr), NoPh e = true → BvarLt 0 e = true →
      Sparkle.Compiler.MachRecUnfold.pass env natLit? isUser e = Except.ok r → NoPh r = true ∧ BvarLt 0 r = true
passWith_ph : （同じ形、∀ (fuel : Nat) が isUser の前）
Inst1Agrees : Prop
ReplaceAgrees : Prop
HeadBetaAgrees0 : Prop
Expr.beta        = fun f args => f.betaRev args.reverse
Expr.headBeta    = fun e => have f := e.getAppFn; if isHeadBetaTargetFn false f = true then f.betaRev e.getAppRevArgs else e
Expr.instantiateLevelParams e ps ls = if (ps.isEmpty || ls.isEmpty) then e else instantiateLevelParamsCore (getParamSubst ps ls) e
Expr.instantiateLevelParamsCore s e = Expr.replace (replaceFn s) e
```

（`ReplaceAgrees` / `HeadBetaAgrees0` は par/rt-abbrev-s1 の `Tools/Assume/AbbrevExtern.lean` の文。scratch は §4 の方法で持ち込んだ上で elaborate。`beta_target` の本体は未証明（scratch の `sorry`）。）

## 2. (b) 新しい仮定: 既存で足りるか

`pass` が呼ぶ core の extern / opaque と、それを覆う仮定:

| 呼び出し | 場所 | 覆う仮定 |
|---|---|---|
| `Expr.instantiateLevelParams` | `iota`（`_sparseCasesOn`、`rec`）、`reduceMatcher?`、`unfoldCall?` | `ReplaceAgrees`（`instantiateLevelParamsCore` は `Expr.replace` そのもの、上の `#print`）。`rec_arm_goodU` / `rnc_ph2` / `ilp_ph`（RT_RECRULE_FREEZE §3、scratch で sorry なし、axioms は propext / Classical.choice / Quot.sound）をそのまま使う |
| `Expr.instantiate1` | `listLit?` の letE の腕、`passStep` の letE の腕 | `Inst1Agrees`（T1L-51）。`inst1Spec_noPh` / `inst1Spec_bvarLt`（`Tools/ShippingGen5ReaderTraceInst1.lean`、base にある）で保存 |
| `Expr.beta f args` | `headBetaM`（`f` はラムダ）、`unfoldCall?`（`f = v`、`v` の形は不明） | 下記 §2.1–2.3 |
| `mkAppN` / `extract` / `instantiate` を直接 | なし（構造的） | 不要 |

### 2.1 `HeadBetaAgrees0` の中身

`NoPh e ∧ BvarLt 0 e` の `e` について `e.headBeta = headBetaSpec e`（`headBetaSpec` は `betaRev` の全域モデル）。保存は定理 `headBeta_good`（par/rt-abbrev-s1、証明済み）。`headBeta` は頭が `isHeadBetaTargetFn false` のときだけ `betaRev` を呼ぶ。引数つきの `Expr.beta f args = betaRev f args.reverse` は、その `f` が頭になる `mkAppN f args` の `headBeta` と同じ呼び出し。

### 2.2 `f` が `isHeadBetaTargetFn false`（ラムダ、または mdata に包まれたラムダ）のとき

`f.beta args = (mkAppN f args).headBeta`（上の `beta_target`）。`(mkAppN f args).getAppFn = f`（`f` が app でない）と `(mkAppN f args).getAppRevArgs = args.reverse` が要り、いずれも `getAppRevArgsAux`（core の private、名前に数値成分がある）の展開で出る見込み。par/rt-abbrev-s1 は同じ private を `unfold_priv` / `priv%`（新規ファイル内の小さな meta 補助）で展開しており（`getAppRevArgs_good`）、同じ手法が使える。**この調査では導出は証明していない**（上の `beta_target` は scratch で `sorry`）。実装で証明できなければ、§2.3 の仮定を `f` の形の制限なしに広げることを coder が reviewer に報告する（新しい freeze になる、自動で広げない）。この場合 `NoPh f ∧ BvarLt 0 f ∧ 各引数 NoPh ∧ BvarLt 0` が `HeadBetaAgrees0` の入力条件。`headBetaM` では `f` が `e` の頭（良い）、引数が `e` の引数（良い）。

### 2.3 `f` が `isHeadBetaTargetFn false = false` のとき（`unfoldCall?` の `v.beta args`）

`v = d.value.instantiateLevelParams ..` は `DeclValuePh` と `ilp_ph` で `NoPh ∧ BvarLt 0` までは分かるが、ラムダとは限らない（この調査では、`_sunfold` の値が常にラムダであることを示す供給元・経路は見つからなかった。成り立たないという意味ではない）。ラムダでなければ `HeadBetaAgrees0` は何も言わない（`headBeta` は `e` を返し、`beta` は `betaRev` を呼ぶ）。`betaRev f revArgs` の `go` は、`f` がラムダでも mdata でもないとき `mkAppRevRange (f.instantiateRange n sz revArgs) 0 n revArgs`（`n = sz - 0 = sz`）で、空の範囲の `instantiateRange` が `f` を返すことと合わせて `mkAppN f args` になる（core `Expr.lean` の `betaRev.go` の読みと、`instantiate_range` の C++ の読み。証明ではない）。

新しい仮定（上の `BetaNonTargetAgrees`）:
* 文: `isHeadBetaTargetFn false f = false` の `f` について `f.beta args = mkAppN f args`。
* なぜ証明できないか: `betaRev` は `partial def`（論理に本体がない）で、`Expr.instantiateRange` は extern。
* 範囲: `f` の形だけに絞り、`NoPh` / `BvarLt` の条件はつけない（`mkAppN` との等式なので不要。条件を足すと弱い仮定になるが、使う側で条件を示す手間が増えるだけ。最小の文を選んだ）。
* 比較（読みであって証明ではない）: core `Lean/Expr.lean` の `betaRev`（v4.32.1）、`kernel/instantiate.cpp` の `instantiate_rev`（空の範囲）。実装時に具体の行番号を `Tools/Assume/` のコメントに書く。
* 台帳: **T1 の新しい候補 +1**（受理されるまで数えない）。登録先は新規 `Tools/Assume/BetaExtern.lean`（または `AbbrevExtern.lean` と同じ namespace の新規ファイル、`AbbrevExtern.lean` の編集は他 Issue の文なので触らない）。
* 代替（不採用、記録のため）: `v.beta args` を `headBetaM` 経由に変える（compiler 変更、ユーザー判断）。`HeadBetaAgrees0` を全 `f` に広げる（U-2 の文の変更。reviewer 承認済みの文なので触らない）。

## 3. (c) 旧 `PassPh`（0e16378b）との関係

旧: `PassPh env := DeclValuePh env → RecRulePhU env → ∀ isUser e, NoPh e → BvarLt 0 e → NoPh (pass ..) ∧ BvarLt 0 (pass ..)`（`pass` が `Except` でなかった頃の型）。inline-compose の消費側は `rounds_ph` / `userInliner_ph` で `hp hv hrr isRec e hn hb` と呼んで `NoPh (pass ..) ∧ BvarLt 0 (pass ..)` を得る。

* 新しい `pass_ph` は旧 `PassPh` を **そのままの型では出せない**（`pass` の戻りが `Except`、仮定が 4 つ多い）。消費側の `rounds_ph` は `userInliner.rounds` の定義（`pass` の結果を `match` で取る）に従うので、`.ok r` の腕で `pass_ph` を使い、`.error` の腕は `rounds` が `e` を返す形ならそれで足りる（実際の定義は 2df5d4d7 の `userInliner.rounds` の読み取り。未確認なら実装時に確かめる）。
* inline-compose 側の文の調整の範囲（他 Issue `sparkle-rt-inline-compose`、別の freeze）: (i) `PassPh` の仮説を外し、`rounds_ph` / `userInliner_ph` に `ReplaceAgrees`（既にある）`Inst1Agrees` `BetaNonTargetAgrees` を足す（`HeadBetaAgrees0` と `ReplaceAgrees` は既にその仮説リストにある）。(ii) `rounds_ph` の `.ok` / `.error` の場合分け。この Issue ではこれらの変更をしない（新規ファイルのみ）。調整の見込み: 型の変更 2 定理、編集 ~20 行。
* この Issue の成果物は inline-compose のファイルに触れない。受理後に別の単位で `PassPh` を外す（親 Issue の完了条件）。

## 4. 持ち込み（ReplaceAgrees / HeadBetaAgrees0 は base にない）

`ReplaceAgrees`（T1L-73 相当の U-1）と `HeadBetaAgrees0`（T1L-74 相当の U-2）は `par/rt-abbrev-s1`（6aa30e51）の `Tools/Assume/AbbrevExtern.lean` にある。base（73e78c8f）は `d68b167c` から 34 コミット先で、abbrev-s1 は `d68b167c` から 4 コミット（796b3ff4, 7aefd1b4, 2afbcc18, 6aa30e51）。scratch では `git cherry-pick -n 796b3ff4 7aefd1b4 2afbcc18 6aa30e51` が競合なしで通り、変更は新規 6 ファイルと `lakefile.lean` の末尾 9 行の追加だけ（すべて新規 / 追記）。`kjob lake build Tools.ScratchPassPh` が `Tools.ShippingGen5ReaderTraceAbbrevS1` まで含めて exit 0 だった。

提案: 実装ブランチの先頭で同じ 4 コミットを cherry-pick する（merge ではない）。cherry-pick / merge はこの freeze の承認とは別に coder と相談（指示どおり）。コミットが残る形（abbrev-s1 が先に受理・統合されれば、実装ブランチはそれを取り込むだけ）なので、統合順が変わっても二重定義にならない。

## 5. (d) 証明の分解と見込みの行数

新規ファイル `Tools/ShippingGen5PassPh.lean`（+ `Tests/Gen5/PassPhCheck.lean`、lakefile に lean_lib 2 件、RT_PASS_PH_PLAN §1 の補題の列）。

| 補題 | 使う仮定 | 行数 |
|---|---|---|
| `beta_target`、`beta_good`（`G f → (∀ a ∈ args, G a) → G (f.beta args)`、場合分け） | `HeadBetaAgrees0`、`BetaNonTargetAgrees`、`headBeta_good` | 60 |
| `headBetaM_good`（燃料の帰納） | `beta_good` | 30 |
| `rnc_ph2` / `ilp_ph` / `rec_arm_goodU`（RT_RECRULE_FREEZE §3、scratch にある） | `ReplaceAgrees`、`RecRulePhU` | 90（`rnc_ph2` は S1 の `rnc_ph` の一般化の写し） |
| `ctorApp_good`、`mkAppN_good` | なし | 50 |
| `iota_good`（燃料の帰納、`M` = `ExceptT String Option` の `stuck` / `.error` は空虚） | `DeclValuePh`、`rec_arm_goodU`、`headBetaM_good`、`ilp_ph` | 90 |
| `reduceMatcher?_good`、`reduceHead_good` | `DeclValuePh`、`iota_good`、`ilp_ph` | 60 |
| `betaAll_good` / `betaSpine_good`（相互、測度 `(fuel, sizeOf, k)`） | `headBetaM_good` | 70 |
| `listLit?_good`（zeta は `Inst1Agrees` + `inst1Spec_noPh/bvarLt`） | `Inst1Agrees` | 60 |
| `evalNode?_good`、`unfoldCall?_good` | 上のすべて | 90 |
| `passM` / `passStep` / `passSpine` の同時帰納（メモの不変量: すべての `(k, v)` で `G k → G v`）、`passWith_ph`、`pass_ph` | 上のすべて | 130 |
| 合計 | | **約 730（見込み 500–800）** |

* `relevant` / `relevantClosure` は式を変えない（`pass` を呼ぶかどうかを選ぶだけ）ので補題は要らない。
* メモ: `passM` の `get?` で返る値は、以前の `passM` が `G k` の入力から作った値。状態を持つ `PM` の不変量を `StateM` の run で運ぶ（`ExceptT String (StateM ..)` の展開）。ここが最も不確かで、全体の見込みの幅の主因。証明が `PM` の `bind` 展開で 120 分の Pod に収まらない場合は、補題を別ファイルに分け、`kjob run` で coder に回してもらう。
* 旧 `PassPh` の名前は新ファイルでは使わない。

## 6. (e) 台帳

| 項目 | FG | T1 | 備考 |
|---|---|---|---|
| 今回の freeze（文書） | −0 +0 | −0 +0 | 何も登録していない |
| `BetaNonTargetAgrees`（新しい T1 候補） | 0 | **+1 候補（相殺しない、受理まで数えない）** | §2.3、登録先は新規 `Tools/Assume` ファイル |
| `ReplaceAgrees`（U-1） / `HeadBetaAgrees0`（U-2） | 0 | abbrev-s1 の freeze の計数のとおり（U-1: T1L-54 の付け替えで ±0、U-2: +1 候補） | この Issue では新しく足さない。再利用だけ |
| `Inst1Agrees`（T1L-51） | 0 | 既存、±0 | |
| `RecRulePhU` | 仮説のまま。登録（FG +1 か N1-a に数えるか）は RT_RECRULE_FREEZE §5 の reviewer 判断 | 0 | この freeze では登録しない（仮説定義だけを新ファイルに置く） |
| 旧 `PassPh`（U-3 候補、**未登録**） | 受理で不要。台帳にも入っていないので数は変わらない（FG 94 から −0） | | 条件: `pass_ph` の受理後に inline-compose が `PassPh` を外す別の単位が受理されること |
| 台帳 | FG 94 / T1 54（今回 FG −0 +0 / T1 −0 +0） | | 条件付き台帳: T1 55（`BetaNonTargetAgrees` が受理されたとき）。受理待ちは台帳に数えない |

## 7. reviewer に確認してほしい点

1. 新しい仮定 `BetaNonTargetAgrees`（T1 +1 候補）の文と範囲（§2.3）。`HeadBetaAgrees0` を触らずに足す形でよいか。
2. `RecRulePhU` を新ファイルの仮説定義のままにし、登録を別の判断に残す（§6）でよいか。
3. 旧 `PassPh` の型を `Except` の `.ok r` 形（`pass_ph`、§1）に置き換えること、`natLit?` を任意にすること。
4. §4 の持ち込み（abbrev-s1 の 4 コミットを cherry-pick）の提案。
5. `beta_target` が証明できなかった場合に止まって報告する（§2.2）扱い。
