# `ConstValueE PT` — freeze 草案（D.D-4、案 B）。草案であり、採用ではない（DCF-1〜3 反映済み、§DCF-4 を末尾に追記）

Issue `sparkle-ledger-dd4`。土台 f00da0d5（par/cvtop）。担当 agent は調査と草案のみ。**TRUSTED も新しい仮定も入れていない。** 判断は reviewer。
Lean の型の骨格: `Tools/ShippingGen5ConstValueE.lean`（定義と型だけ。定理なし、sorry なし、axiom なし。build ok）。
残余の測定: `Tests/Gen5/PrimResidueCount.lean`（meta、`logInfo` で集計だけ。**59 宣言のサンプル**）。生の測定は KJOB_REPORT_PATH 側に置き、この文書には集計と上位名だけを書く。

## 1. 規則の全一覧

記法: `ρ` は値の環境（`Val := List Entry`、`Entry = ⟨τ : Expr, d : Dyn⟩`、de Bruijn で先頭が bvar 0）。`τ` は**構文上の型**（`Expr`）、`α` は Lean の型、`v : α`。
`CVE env ρ e τ α v` は「項 `e`（構文上の型 `τ`）が Lean の値 `v : α` を意味する」。`TDen env ρ τ T` は「型式 `τ` が Lean の型 `T` を意味する」。両者は相互帰納（骨格は `mutual`、Prop）。
`ConstValueE PT env X α v := ∃ ls τ, CVE PT env [] (.const X ls) τ α v`（`ConstValueRel` と同じ型）。

### 1.1 項の規則 `CVE`

| 規則 | 前提 | 結論 | 備考 |
|---|---|---|---|
| natLit | なし | `CVE ρ (lit n) (const Nat) Nat n` | `Nat` の型の形成規則は TDen の tcon（表の行） |
| strLit | なし | `… (lit s) (const String) String s` | 同上 |
| bvar | `ρ[i]? = some en` | `CVE ρ (bvar i) (en.τ.liftLooseBVars 0 (i+1)) en.d.ty en.d.val` | lift の整合は補題（§3 (c)） |
| lam | `TDen ρ A TA`、`TB : TA → Type`、`f : (a:TA) → TB a`、`∀ a, CVE (⟨A,⟨TA,a⟩⟩::ρ) body B (TB a) (f a)` | `CVE ρ (lam n A body) (forallE n A B) ((a:TA)→TB a) f` | 全称の前提で、存在を選択しない |
| app | `TDen ρ A TA`、`∀ a, TDen (⟨A,⟨TA,a⟩⟩::ρ) B (TB a)`、`CVE ρ fe (forallE n A B) ((a:TA)→TB a) fv`、`CVE ρ x A TA av`、**頭が const でない** | `CVE ρ (app fe x) (B.instantiate1 x) (TB av) (fv av)` | 型は依存（`TB av`） |
| let | `TDen ρ A TA`、`CVE ρ v A TA av`、`CVE (⟨A,⟨TA,av⟩⟩::ρ) b B TB bv` | `CVE ρ (letE n A v b) (B.instantiate1 v) TB bv` | |
| const-unfold | `env.find? c = some (.defnInfo d)`、`CVE ρ ((d.value.instantiateLevelParams d.levelParams ls).beta args) τ α v` | `CVE ρ (mkAppN (const c ls) args) τ α v` | **spine 全体**に対する規則（構文的 β）。停止性の主張はない（導出が証拠） |
| const-prim | `env.find? c = some ci`、`PT.tms c = some row`、`¬ IsDefn env c`、`ArgsDen ρ row.kinds args as`、`row.den as = some d`、`TDen ρ τres d.ty`（行の型付け義務） | `CVE ρ (mkAppN (const c ls) args) τres d.ty d.val`。`τres = instForall (ci.type.instantiateLevelParams …) args`（型は表でなく **env** から） | spine 全体 |

### 1.2 型の規則 `TDen` と引数 `ArgsDen`

| 規則 | 前提 | 結論 |
|---|---|---|
| pi | `TDen ρ A TA`、`TB : TA → Type`、`∀ a, TDen (⟨A,⟨TA,a⟩⟩::ρ) B (TB a)` | `TDen ρ (forallE n A B) ((a:TA)→TB a)` |
| tcon（型の基本形 `TypeDenotes`） | `PT.tys c = some row`、`¬ IsDefn env c`、`ArgsDen ρ row.kinds args as`、`row.den as = some T` | `TDen ρ (mkAppN (const c ls) args) T` |
| tunfold | `defnInfo`、`TDen ρ (value.beta args) T`（`abbrev` 型など） | `TDen ρ (mkAppN (const c ls) args) T` |
| ArgsDen.nil / .ty / .tm | `row.kinds` が `false` の引数は `TDen`、`true` の引数は `CVE`（項を `Arg.tm ⟨α,v⟩` に） | 引数列の対応 |

`Sort`（`Type`）を束縛する pi（`{α : Type}`）の値は `Type 1` の値になり `Dyn`（`Type 0` のみ）に入らない。この草案は**型引数を値にしない**: 多相定数は spine 全体で展開（unfold）/ 表（prim）し、型引数は `TDen` の引数として消費する。
型をまたぐ rank-2 の引数（型に関する lambda を値として渡す）は導出できない（範囲外）。コーパスでの頻度は未測定（§6）。

### 1.3 unfold と prim の排他条件

- 骨格では**定数の kind で分ける**: unfold は `env.find? c = some (.defnInfo _)`、prim と tcon は `¬ IsDefn env c`。したがって一つの `c` は unfold か prim のどちらか一方だけで、`c ∉ PT.dom` のような表の中身に依存しない（rev5 の R2 の懸念への直接の答え。表が名前ごとに 1 行であることは不要）。
- 案 B の表は定義上 defnInfo の行を持たない（最大展開）。表の `defnInfo` の行は、あっても規則が使わない（無害）。
- **app は頭が const でない spine にだけ**適用する。const 頭の spine は unfold / prim が spine 全体で扱う。これがないと、同じ式に app の導出と unfold の導出ができ、両者の一致（合流性）の証明が要る。
- 部分適用された prim（`Prod.mk a` を関数として渡す等）は規則がない（spine が `kinds.length` と等しい場合だけ prim）。η 展開の規則を足すかは §6 の項目。

## 2. 関数性 `ConstValueFunctional (ConstValueE PT)` の証明計画

`∀ env c (α β) v w, CV env c α v → CV env c β w → α = β ∧ HEq v w`（`ShippingGen5FG.lean:22`）。次の 4 項。

- **(a) 規則の全一覧の freeze**: §1。骨格が型として通ることは確認した。
- **(b) 排他性**: §1.3。kind による分割（`IsDefn` と `¬ IsDefn`、頭が const か否か）。各ケースで他の規則が前提と矛盾するので、帰納法の場合分けは規則ごとに 1 つに決まる。補題: `mkAppN` の頭と引数列は一意（`getAppFn`/`getAppArgs`）。
- **(c) 決定性**: 次の補題が要る。
  1. `TDen` の関数性: `TDen ρ τ T → TDen ρ τ T' → T = T'`。pi は `TB` を `funext` で一致させる（`funext` は標準 axiom `Quot.sound` で導出される。追加の仮定ではない）。
  2. **構文上の型 `τ` を添字に持たせた理由（設計上の最重要点）**: Lean は Pi 型の単射性 `((a:A)→B a) = ((a:A')→B' a) → A = A'` を証明できない。型を Lean の `Type` だけで持つ設計（`Dyn` だけ）では、app の場合に `fv` の型の等式から引数の型の等式が取れず、関数性が証明できない。そこで `τ : Expr` を添字にし、`α` は `TDen ρ τ α` で決まる（1. で一意）ようにした。app/lam の前提は `TA`/`TB` を TDen の導出の部品として陽に持つ。
  3. `liftLooseBVars` / `instantiate1` と環境 `ρ` の整合（`TDen`/`CVE` が構文上の型の置換と両立する補題）。**関数性そのものには不要だが、規則が健全であること（ `τ` が Lean の型付けと一致すること）の説明に要る**。規模の見積もりが最も不確実な部分。
  4. 行の決定性: `row.den` は関数なので自動。
  5. `HEq` の扱い: lam の `f`、app の `fv av` は `TB` の一致のあと `HEq` から `Eq` へ落とす補助補題。
- **(d) 帰納法**: 二つの導出 `CVE … α v` と `CVE … β w` に対する同時帰納（`ρ`, `e`, `τ` を固定して `α = β ∧ HEq v w`。`τ` が添字なので、結論は `α = β` の部分を TDen の関数性から得て `v ≍ w` を導出の形で示す）。bvar/lit は直接、lam は全称前提と `funext`、app は IH を `fe` と `x` に使い `TA = TA'`（TDen の関数性）のあと `TB = TB'`、let は IH 2 回、unfold は IH 1 回（同じ spine から同じ `beta` 結果。入力が同じ）、prim は `hargs` の IH（`ArgsDen` の関数性）と `row.den` が関数であること。

## 3. Lean の型の草案（Dyn 宇宙、依存 app）

骨格 `Tools/ShippingGen5ConstValueE.lean` のとおり。要点:

- `Dyn := ⟨ty : Type, val : ty⟩`（`Type 0` のみ）。`DeclConnect` の `sh.Ty : Type` と一致する宇宙。
- 表 `PrimTable := { tys : Name → Option TyRow, tms : Name → Option TmRow }`。名前ごとに高々 1 行（`Option`）。行は spine 全体の引数列 `List Arg`（`Arg := tm Dyn | ty Type`）から値を作る関数。普通の `def`、axiom は入らない。
- 依存 app: 結果の型は `TB av`（`TB : TA → Type`）、構文上の型は `B.instantiate1 x`。
- 骨格で確かめたこと: 相互帰納（`TDen`、`ArgsDen`、`CVE`、すべて Prop、添字に `Type` と `Expr`）が elaborate する。strict positivity と宇宙の問題はない。
- 確かめていないこと: 規則の**健全性**（TDen/CVE が Lean のカーネルの型付けを正しく写していること）、関数性、`ConstValueOk` 型の義務、既存の `declConnect_eq` との接続（型は `ConstValueRel` と同じなので差し込めるはず）。
- 変更が要りうる点: `Dyn` を `Type 0` に限ったので、`Type 1` 以上の値を意味にする宣言（宇宙多相の値の引数など）は導出できない。`sh.Ty` の断片（`Signal D Bool`、`Signal D (BitVec n)`、`Prod`、`→`）は `Type 0`。

## 4. 行数の見積もり（**測っていない推定**）

| 単位 | 内容 | 行 |
|---|---|---|
| DCF-1 | 規則・`TyRow`/`TmRow`/`PrimTable`・`instForall`（骨格を整える） | 150〜250（骨格は約 130 行） |
| DCF-2 | `TDen`/`ArgsDen` の関数性（`funext`、`HEq` 補助） | 200〜350 |
| DCF-3 | `CVE` の関数性（同時帰納、排他の場合分け、spine 補題） | 400〜800 |
| DCF-4 | 規則の健全性（lift/instantiate と構文上の型）。**要否は reviewer 判断** | 300〜700 |
| DCF-5 | 表の行の生成（meta）と、行ごとの型付け補題 `hty` の検査 | 行数に比例（残余 100〜200 行。§5 の数）。1 行 5〜15 行の定義 + 型付け |
| 計 | | 約 1,200〜2,500 行（rev5 の見込み 1〜2 千行と整合） |

## 5. 残る定数の数え上げ（サンプル）

**サンプルであることの明記**: 対象は `Tests.Compiler.ShippingMachine{Seq,Inst,SeqLoop,Loop,Comb,Raw,Tele,Nest,Fuse,Linked,SeqLinked,MemLinked,Norm,Closes,DepthH}Test` と `ShippingSignOpsTest` の import で環境に現れる、`X.machine_source` を持つ（コンパイラが成功した）**59 宣言**。
全コーパス（Tests 全体、`design`/`gate` ルート）ではない。測定は `Tests/Gen5/PrimResidueCount.lean`（build ok、`kjob lake build Tests.Gen5.PrimResidueCount`、各宣言の値から `defnInfo` を最大まで展開）。
証明項（定理が頭の適用）は入らない。定義の値だけを走査し、型（`ci.type`）は走査していない。

| 分類 | 異なる定数（59 宣言の和） |
|---|---|
| コンストラクタ | 76 |
| 再帰子 | 11 |
| quot | 0 |
| opaque / extern / implemented_by（opaque） | 0 |
| opaque（plain） | 0 |
| 型の基本形（inductive 型） | 66 |
| axiom | 0 |
| **計（残余）** | **153** |

- 1 宣言あたりの残余の最大は 116。59 宣言すべてが共通に使うのは 39 定数（`Bool`, `Nat`, `Eq`, `Decidable`, `Prod` 系、`Signal`、`DomainConfig`、`HAdd/Add/LE/LT` の構造体、`Functor`、`Inhabited` など）。
- 上位の残余（59 宣言すべてに現れる）: `Nat`, `Nat.zero`, `Nat.succ`, `Nat.rec`, `Nat.le`, `Bool`, `Bool.true/false`, `Bool.rec`, `Decidable.isTrue/isFalse`, `Decidable.rec`, `Eq`, `Eq.refl`, `Eq.rec`, `False.rec`, `HAdd.mk`, `Add.mk`, `LE.mk`, `LT.mk`, `Functor.mk`, `Inhabited.mk`, `Sparkle.Core.Signal.Signal`, `Sparkle.Core.Signal.Signal.mk`, `Sparkle.Core.Domain.DomainConfig`。
  再帰子 11: `Bool.rec, Decidable.rec, Eq.rec, False.rec, Nat.rec`（59）、`Nat.le.rec`（56）、`List.rec`（44）、`BitVec.rec`（30）、`PSigma.rec`（19）、`Prod.rec`（5）、`Int.rec`（1）。
- ユーザー定義の構造体の型と構成子（例 `CntOut(.mk)`, `HFTOut(.mk)`, `HttpEmitOut(.mk)`）が 17 定数。宣言ごとに 1 組ずつ増える（コーパスが増えると残余も増える）。残りの約 136 はライブラリ（core / Sparkle.Core）で固定。

### 質問への答え（Signal.register / Signal.loop / BitVec 演算）

| 定数 | env 上の種別 | 残余に入るか |
|---|---|---|
| `Sparkle.Core.Signal.Signal.register` | `defnInfo`（plain） | **入らない**（展開できる）。表に行は要らない |
| `Sparkle.Core.Signal.Signal.loop` | `defnInfo`（`@[implemented_by loopImpl]` 付き）。値は `loopGo` 経由 | **入らない**（展開できる。59 宣言すべてで展開）。`loopImpl` は実行用の実装で論理の値は展開した定義。意味としては**論理上の定義**を採ることになる（`implemented_by` の実装ではない）。この選択が意図どおりかは reviewer の確認項目 |
| `Signal.registerWithEnable` / `mux` / `loopGo` | `defnInfo` | 入らない |
| `Signal.memory` | `defnInfo`（`@[implemented_by memoryImpl]`、1 宣言で展開） | 入らない（同上） |
| `BitVec.add/and/ult/ofNat/extractLsb'/append/toNat`、`Bool.and`、`ite`、`HAdd.hAdd` | `defnInfo` | 入らない。展開の先で `Nat.rec`/`BitVec.ofFin`/`Fin.mk` などの残余に至る |
| `Nat.add`、`Nat.mod` | `defnInfo`（`extern` 付き） | 入らない（展開）。カーネルの GMP 加速は論理的には展開と同じ |
| `Prod.mk` | コンストラクタ | **入る**（54 宣言） |
| `Signal`（型） | inductive（構造体） | **入る**（59 宣言） |

`opaque` / `extern` で展開できない定数は、このサンプルの値には現れなかった（opaque 0）。`Signal.cacheGet` などの `extern` opaque は `loopImpl` の中にだけあり、論理の定義 `loopGo` を展開する限り入らない。

### 測定の限界（正直に）

- サンプル（59 宣言、16 モジュール）。全コーパスではない。`design`/`gate` ルートの宣言と、他の Test モジュールの宣言は入っていない。
- 定義の値だけを走査した。型の中の定数（型式の依存）は、値の中の束縛の型として現れる限りでのみ数えた。
- 証明項を数えない近似は「定理が頭の適用に入らない」であり、`Eq.mpr`/`cast` に入った証明由来の定数は数えうる。上の `Eq.rec` はその例かもしれない（カーネルの規則としては必要になりうる）。
- 「実際にコンパイラが成功する」は `X.machine_source` の存在で代用した（`#machine_endpoint` 系の成功の副産物）。
- 部分適用された prim が現れるか、rank-2 の型引数が現れるかは測っていない。

## 6. 結論

- **残余の数**: サンプルで 153（コンストラクタ 76、再帰子 11、型の基本形 66、quot / opaque / extern / axiom は 0）。ライブラリ由来が約 136、宣言ごとのユーザー構造体が 17。コーパスを広げると増える見込み（主にユーザー構造体と、`List`/`Int`/`PSigma` などの再帰子・型）。
- **TRUSTED が要る行の候補一覧**: 表の行はどれも「`Name` というデータ = Lean の定数」という対応で、これだけは Lean の論理の中で証明できない（行の型付け `hty` は行ごとに**証明できる**義務にしたので、信頼が要るのは名前の対応だけ）。候補はクラスで三つ:
  1. コンストラクタ 76（`Prod.mk`, `Bool.true/false`, `Nat.zero/succ`, `Signal.mk`, `DomainConfig.mk`, 構造体の `*.mk`、`Decidable.isTrue/isFalse`, `Eq.refl` など）。
  2. 型の基本形 66（`Nat`, `Bool`, `BitVec`, `Prod`, `Eq`, `Signal`, `DomainConfig`, `HAdd`, …）。
  3. 再帰子 11（`Nat.rec`, `Bool.rec`, `Eq.rec`, …）。ただし再帰子は表の行ではなく、`RecursorVal.rules` に基づく**反復規則（iota）**として規則に書けるかもしれない（motive が `Sort u` を取るので `Type 0` の `Dyn` では表せない。規則として spine で書く方が自然）。これは未調査で、独立の単位（DCF-6）にできる。
- **表なしで済む範囲**: `Signal.register` / `Signal.loop` / `Signal.mux` / `Signal.memory`、`BitVec.*`、`Bool.*`、`ite`、`Nat.add` など、`defnInfo` である全定数は展開で扱える（表なし）。したがって「Signal 基本操作が表に要る」という懸念（CV_FIX_DECISION §4.1）は、このサンプルでは外れた。
  表が要るのは、**展開できない定数だけ**（コンストラクタ・型の基本形・再帰子）。この範囲は小さく一様で、`ConstantInfo` の kind から機械的に列挙できる（行そのものは meta で生成できるが、名前の対応が信頼される点は変わらない）。
- **次の単位**（提案。採用は reviewer）:
  1. DCF-1/2: 骨格の整備と `TDen` の関数性（TRUSTED なしで進められる）。
  2. DCF-3: `CVE` の関数性（表 `PT` を任意のパラメータのまま。`PT` の中身に依存しない定理にできる。TRUSTED の判断を待たなくてよい）。
  3. 残余の拡大測定（全コーパス。`design`/`gate` ルート。部分適用 prim と rank-2 の有無）。
  4. 再帰子を規則（iota）で書けるかの調査。書ければ TRUSTED の候補は 型の基本形とコンストラクタの 2 クラスに減る。
  5. TRUSTED（G-PRIM）の採否は、4 と 3 の結果で行を確定してから改めて判断する（今回は承認を求めない）。
- 関数性の定理 `ConstValueFunctional (ConstValueE PT)` は **PT が何であっても**成り立つ形を目標にできる（排他性が env の kind で決まるため）。これは「表の中身が正しいか」と独立で、D.D-4 の欠陥（`CV` が全称の自由な関係）はこの定義への固定で解消される。表の正しさは別に残る。

## 7. 主張しないこと

- 規則が Lean のカーネル意味論に**健全**であること（DCF-4 の対象。未証明）。
- 関数性（未証明。計画のみ）。
- 残余の数がコーパス全体の数であること（59 宣言のサンプル）。
- 新しい TRUSTED の採用・必要性（行の一覧は候補。採否は別判断）。
- 台帳の数の変更（FG 75 / T1 57 のまま。今回 FG -0 +0 / T1 -0 +0）。

## DCF-1〜3 の結果と §DCF-4（健全性）に向けて気づいたこと

Issue `sparkle-ledger-dd4-dcf`。土台 c63f2284。PT は任意のパラメータのまま、TRUSTED・axiom・sorry なし。

### 済んだこと

- 定理（`Tools/ShippingGen5ConstValueE.lean`）: `tden_fun` / `argsden_fun` / `cve_fun`。`∀ PT env`、前提は二つの導出だけ。排他性は規則の前提（`IsDefn` / `¬IsDefn`、app の `hnh`）が担うので PT の中身に依存しない。結論は `τ = τ' ∧ α = β ∧ HEq v w`（τ の一意性を含める。理由は下）。系 `constValueEAt_functional`（`ls` を固定した `ConstValueE`）。
- 骨格に入れた変更（§1 の表からの差分）: (1) natLit/strLit の型の level を `[]` に固定（任意の `ls` だと τ が一意にならない）。(2) lam に `a0 : TA`（定義域の元）を要求。(3) unfold/prim/tcon/tunfold の結論の添字を変数にして `he : e = mkAppN …` の等式を前提に持つ（`cases` で一致させるため。意味は同じ）。
- `TDen`/`ArgsDen` の関数性は単独では示せない。`ArgsDen.tm` が `CVE` を含み、`CVE.app` が `TDen` を使うので、3 つの同時帰納（相互再帰）。DCF-2 と DCF-3 は実質 1 つの定理。
- Check: `Tests/Gen5/DCFCheck.lean`（型の構造照合、負対照、`#print axioms` は propext / Classical.choice / Quot.sound のみ）。

### §DCF-4 に書くこと（未着手。気づいた点）

1. **τ の一意性が関数性に必須**。固定した τ だけで関数性を言うと app が通らない（結論の τ = `B.instantiate1 x` から `A`、`B` が決まらず、`fe` の IH が使えない）。そこで `cve_fun` は τ の一意性を結論に含める。これを成り立たせるために (1)(2) の規則変更が要った。(2) の代償: 空の型を定義域とする lam は導出できない。
2. **`∃ ls` の `ConstValueE` の関数性は未証明**。`ConstValueRel`/`ConstValueFunctional` は level が存在量化で、`const X ls` と `const X ls'` は別の式なので `cve_fun` は直接使えない。規則は level を `instantiateLevelParams` 以外で見ないので、level を消す対応（書き換えの下で導出が保たれる補題）で示せるはずだが、`instantiateLevelParams` と `beta`/`instantiate1` の可換が要る。`ConstValueE` を `ls` 固定（または `ls = []`）にする選択肢もある。DeclConnect に差し込む前に決める必要がある。
3. **健全性は未証明**: 構文上の型 τ と `ConstantInfo.type` の整合（`bvar` の `liftLooseBVars`、app の `instantiate1`、prim の `instForall`、`hty` が表の行の義務のままでよいか）。lam の `B` と `TB` の対応は規則が前提として持つだけで、カーネルの型付けとの一致は未確認。
4. **`Dyn` が `Type 0` のみ**の制約と、型引数を値にしない設計は変えていない（§1.2）。
5. `cve_fun` は `hty`（prim の型付け義務）を使わない。つまり `hty` は関数性には不要で、健全性の側の義務。

### 主張しないこと（追加）

- 規則の健全性、`ls` が存在量化の `ConstValueE` の関数性、`DeclConnect` への接続。台帳の数は変わらない（FG 75 / T1 57、今回 FG -0 +0 / T1 -0 +0）。

## §DCF-4 の結果（Issue `sparkle-ledger-dd4-dcf4`、土台 5f4edce4）

TRUSTED・axiom・sorry なし。PT は任意のまま。**設計の変更は reviewer の判断**（下の 1.3）。

### 1. `∃ ls` の `ConstValueE` の関数性 — 現設計では未解決（`LS env X` で迂回、§LS）

1.1 **理由（確認済み）**: level を消す対応の証明には、`instantiateLevelParams`・`instantiate1`・`beta` が level の消去と可換であることが要る。
`Lean.Expr.instantiate1` / `instantiate` / `instantiateRange` / `liftLooseBVars` は **`opaque`（extern C）**で、論理の中に展開がない（`#print` で確認、`Tests/Gen5/DCF4Check.lean`）。
したがって「`erase (b.instantiate1 x) = (erase b).instantiate1 (erase x)`」型の補題は、**現在の API と導出では可換補題が得られず、未解決**（`opaque` の展開がないので、Lean の論理の中の定義から導けない）。証明不能と断定するものではない。可換補題を別の道（`instantiate1` を使わない再定義など）で得られるかは未調査。axiom（=TRUSTED）にする案は reviewer が承認していないので入れない。
（`instantiateLevelParams` 自体は Lean 側の定義 `replace` だが、unfold の本体が `beta` を通るので、`beta` で止まる。）
補題の型は `OblLevelErase`（`Tools/ShippingGen5ConstValueESound.lean`、`Prop` の def。仮定していない）。

1.2 同じ制約で、`ConstValueE`（`∃ ls`）の関数性は、`const X ls` と `const X ls'` の導出の対応が取れず、現在の API と導出では未解決。`ls` を固定した `constValueEAt_functional`（承認済み）は成り立つ。

1.3 **ls を固定する設計案**（採用は reviewer）:
- `ConstValueE PT env X α v := ConstValueEAt PT env X [] α v`（`ls = []`、`∃ ls` を消す）。または `ls` を定数ごとの関数 `LS : Name → List Level` として `PrimTable` の外に取り `ConstValueEAt PT env X (LS X) α v`。
- 型への影響: `ConstValueRel := Environment → Name → (α : Type) → α → Prop` は **変わらない**（`ls` は定義の内側にあり、型に出ない）。`ConstValueFunctional (ConstValueE PT)` は `constValueEAt_functional` からそのまま出る。`DeclConnect` / `declConnect_eq` / `declConnect_of_rows` は `CV` を引数に取るだけなので**変更なし**。
- 意味への影響: universe 多相の定数を `ls = []` で使うので、level パラメータを持つ定数は `instantiateLevelParams` で全 level が潜在的に未置換（`Level.param` のまま）になる。`Type 0` の `Dyn` と `row.den`（level を見ない）では、level の違いは値に現れないので、`ls = []` で導出が止まるのは `ls` が値の型 `Type 0` への制約として働く定義だけ（例: `ULift.{u}` の `u` を 0 以外で使う）。コーパスでの頻度は未測定。`LS` を関数にする案は、この場合を呼び出し側が選べる。
- 代替（不採用の見込み）: level 消去の補題を **axiom** で入れる。reviewer が TRUSTED を承認していない（G-PRIM と同様）ので入れない。

### 2. 規則の健全性（τ と `ConstantInfo.type` の整合）

証明した（`Tools/ShippingGen5ConstValueESound.lean`、axiom は `propext` のみ）: `instForall_nil` / `instForall_cons_forallE` / `instForall_of_not_forallE` / `instForall_append` / `instForall_length_zero`（prim の型 `instForall (ci.type.instantiateLevelParams …) args` の純構文部分）。

**名前付きの義務**（型は書いた。`Prop` の def。仮定も sorry もない。カーネルの型付け `Ty env Γ e τ` は core に Prop がないのでパラメータ）:

| 義務 | 内容 | 未解決の理由 |
|---|---|---|
| `OblLiftClosed` | 閉じた型の `liftLooseBVars` は恒等 | `liftLooseBVars` が opaque（現在の API では補題が得られず未解決） |
| `OblBvar Ty` | bvar の型 = `Γ[i]` の `liftLooseBVars 0 (i+1)` | カーネルの bvar 規則。`Ty` と `liftLooseBVars` |
| `OblApp Ty` | app の型 = `B.instantiate1 x` | `instantiate1` が opaque（未解決）、`Ty` はカーネル |
| `OblLam Ty` | lam: body の型 `B` が codomain | `Ty`（カーネル）。規則側の `B`/`TB` の対応は `CVE.lam` の前提 |
| `OblConst Ty` | 定数の型 = `ci.type.instantiateLevelParams ci.levelParams ls` | `Ty`（カーネル）。unfold の型保存は defeq 側 |
| `OblRowTyped PT env` | prim の `hty`（表の行ごと） | 行ごとの義務（reviewer の許可どおり表の行に残す） |
| `OblLevelErase erase` | 1.1 の level 消去の可換 | 1.1（未解決。ls を固定して迂回する。§LS） |

健全性の定理（`CVE … → Ty env (ρ.map τ) e τ`）はこれらの義務を仮定にして書けるが、仮定つきの定理は入れない（指示）。また unfold の型保存は β/δ 同値（defeq）を含み、`Ty` に変換規則が要る（規模が大きい）。**まとめ: 健全性のうち現時点で証明できたのは `instForall` の構文部分だけで、残りは opaque なカーネル関数と `Ty` に起因する名前付き義務。**

### 3. Check と台帳

`Tests/Gen5/DCF4Check.lean`（構造照合・負対照・`#print axioms`・opaque の確認）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## §LS: 決定的な level 選択 `LS env X`（Issue `sparkle-ledger-dd4-ls`、土台 458993c6）

reviewer の判断: `ls = []` にはしない。各 `(env, X)` に決定的な level 列 `LS env X` を選び、`ConstValueEAt PT env X (LS env X)` を `CV` にする（universe-polymorphic な定数を最初から排除しない）。`OblLevelErase` は仮定にも axiom にもしない（ls を固定して迂回）。健全性の義務（`OblLiftClosed` / `OblBvar` / `OblApp` / `OblLam` / `OblConst` / `OblRowTyped`）は未証明・未仮定のまま。TRUSTED・axiom・sorry なし。`PT` は任意。

### 定義と定理（`Tools/ShippingGen5ConstValueELS.lean`）

- `LS env X := match env.find? X with | some ci => ci.levelParams.map (fun _ => Level.zero) | none => []`。
- `CVLS PT := fun env X α v => ConstValueEAt PT env X (LS env X) α v`。型は `ConstValueRel`（`Environment → Name → (α : Type) → α → Prop`）のまま、`PT` 以外の引数・仮定なし。
- `cvls_functional`: `constValueEAt_functional` から。`∀ PT, ConstValueFunctional (CVLS PT)` が出る。補題 `LS_length`（`ls` の長さ = `levelParams` の長さ）、`LS_none`。
- 選択の理由: `Level.zero` は値の型 `Type 0`（`Dyn`）と合う。levelParams の長さが合うので `instantiateLevelParams` が全 param を置換する。別の選択（param をそのまま残すなど）にしても、定理は `LS` の中身に依存しないので差し替えられる。
- 限界: 規則は `const X ls` の `ls` を `instantiateLevelParams` 以外で見ないので関数性は通るが、`LS` が選ぶ level が `Type 0` の制約を満たさない定数（`ULift.{u}` で `u ≠ 0` が要る使い方など）では導出が止まる。止まることは `DeclConnect` の存在行が作れない（`CVLS` が成り立たない）ことを意味し、矛盾ではない。

### 実コーパスの測定（`Tests/Gen5/LSCorpus.lean`、**59 宣言のサンプル**、PrimResidueCount と同じ root）

測定 (B) は忠実な走査: `(X, LS env X)` から始め、`defnInfo` を `instantiateLevelParams` で展開し、到達した `(const, ls)` を数える（証明項は入れない近似、`Level.normalize` で同一視）。

- **root 自身の levelParams を持つ宣言: 0 / 59**。よって `LS env X = []` で、`∃ ls` の選択と一致する。DeclConnect の存在行（`X` は root）に効く `ls` の選択は、このサンプルでは `[]` に決まる。
- (A) 到達した定義の本体にある `const c ls` の `ls`（生、のべ）: 空 112117 / すべて zero 30233 / 閉じた非零 20387 / param のみ 10015 / param を含む式 3008。ライブラリ定数の使用は、そのまま展開の中で具体的な level に置換されるので、`LS` が選ぶのは root の level だけで足りる。
- (B) 到達した異なる `(const, ls)` は のべ 15396。**同じ名前が異なる ls で到達する箇所**: 13 名、全 59 root で何かは起きる。例（root 数、ls の種類）: `Bool.rec`/`Bool.casesOn`（59, `[0]` と `[1]`）、`Nat.rec`（59, `[1]` `[2]`）、`False.elim`/`False.rec`（56）、`List.rec`/`List.below`/`List.brecOn`（44）、`PProd`/`PProd.mk`（44, 3 種）、`PUnit`/`PUnit.unit`（44）。
  - これは **`LS env X` の選択の問題ではない**。`X` ごとの level を `LS` が選ぶのは root（と `DeclConnect` が参照する名前）だけで、内部の使用は本体の `const c ls` が持つ `ls`（式の側の情報）。複数の ls を持つのは、同じ再帰子・型が motive の宇宙の違う箇所で使われるから。規則は `ls` を式から受け取る（`CVE.const` の `ls` は式の一部）ので、複数の ls を持つこと自体は関数性に影響しない。
  - **効く点**: 型の基本形・コンストラクタ・再帰子（残余、§5）の行 `PT` は、`(Name, ls)` ごとの行になる。`Name` だけの行では足りないので、行の鍵は `Name` ではなく `Name × List Level`（または level 全称の行）にする必要がある（表の設計への示唆。未決定）。
  - DeclConnect の存在行には効かない（root は monomorphic）。
- 限界: 59 宣言のサンプル（`design`/`gate` ルート、他の Test モジュールは入っていない）。到達先の `TgtRun` の呼び出し先を root 以外まで調べていない。polymorphic な root を持つコーパスでは再測定が要る。

### 主張しないこと

- 規則の健全性、`OblLevelErase` の解決。台帳の数は変わらない（FG 75 / T1 57、今回 FG -0 +0 / T1 -0 +0）。
- Check: `Tests/Gen5/LSCheck.lean`（`CVLS PT : ConstValueRel`、追加仮定なし、負対照、`#print axioms` は propext / Classical.choice / Quot.sound のみ）。

## §Key: `PrimTable` の key（Issue `sparkle-ledger-dd4-key`、土台 68acad1e）

reviewer の方針: LS env X は承認済み。最終 carrier と健全性は未承認。TRUSTED・axiom・sorry なし。`PT` は任意のパラメータのまま。
現行 `PrimTable` は `Name` だけが key なので、同じ名前が異なる ls で現れる 13 名（§LS）を表せない。2 案を比べる。

### 1. 2 案の比較

| 項目 | 案 K1: key = `Name × List Level` | 案 K2: level-polymorphic row（row が `List Level` を引数に取る） |
|---|---|---|
| 型 | `tms : Name → List Level → Option TmRow`（`tys` も同様） | `tms : Name → Option (List Level → TmRow)` |
| 関数性の証明への影響 | `prim`/`tcon` の前提が `PT.tms c ls = some row` になるだけ。`spine_inj` が `c = c' ∧ ls = ls' ∧ args = args'` を既に返すので、証明は `cve_fun` と**同じ形**で通る（`cvek_fun`、書き換えは型名と `PT.tms c ls` のみ）。 | 前提は `PT.tms c = some f`、row は `f ls`。`spine_inj` のあと `f ls` が同一になるので同様に通る。 |
| 排他条件（unfold と prim） | 変更なし。kind（`IsDefn env c` と `¬ IsDefn env c`）と app の `hnh` が担う。key が増えても `IsDefn` は `Name` だけで決まる。 | 変更なし。 |
| 表の行数 | **(name, ls) の組ごとに 1 行**。コーパスで現れる組の数だけ（有限、下の測定）。`ls` ごとに別の row を書ける。 | **name ごとに 1 行**（Name-only と同数）。1 行の中で `ls` を引数に取る。 |
| 健全性の義務 `OblRowTyped` の形 | key ごと: `∀ c ls ci row … , env.find? c = some ci → PT.tms c ls = some row → … → TDenK … (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty`（`OblRowTypedK`、`Prop` の def、仮定していない）。行は有限個の key に対して個別に確かめる。 | `ls` を全称にした義務: `∀ ls, …`。`ls` がどの長さ・値でも成り立つ row を書く必要があり、`Type 0` の `Dyn` に収まらない level（`Bool.rec.{2}` など）では `row.den` が `none` を返すことで義務を逃がす形になる。row を書く側の負担が大きい。 |
| 13 名の扱い | `(Bool.rec,[0])` と `(Bool.rec,[1])` を**別の key・別の row**で表す。他の ls には行を置かない（導出が止まる = 存在行が作れない。矛盾ではない）。 | 1 つの row が `ls` を見て振る舞いを分ける。 |
| 相互の関係 | K2 は K1 の特殊形（`PrimTableK.ofPoly`）。Name-only は K1 の特殊形（`PrimTable.toK`）。 | 同左。 |

### 2. 推奨: K1（`Name × List Level`）

1. **一般性**: K1 は K2 と現行 `PrimTable` の両方を含む（`PrimTableK.ofPoly`、`PrimTable.toK`。後者は `cve_toK` で導出が移る）。逆は成り立たない（K2 は全 `ls` で row が存在する形）。
2. **義務が有限・局所**: `OblRowTypedK` は key ごと。`ls` を全称にする K2 の義務は、`Type 0` の `Dyn` に収まらない level を `row.den = none` で逃がす書き方を強いる。K1 では置いた key にだけ義務が生じ、置かない key は導出が止まるだけ。
3. **meta で行を生成しやすい**: 行は `(name, ls)` の組を列挙して作れる（測定がそのまま行の一覧になる）。
4. **代償**: 行数が増える（下の測定: Name-only との差が追加行）。`ls` が `Level.param` を含む組が出るとキーが開くが、`LS` が root の level を閉じた値にするので、測定では閉じていない key の数を数えた。
5. 関数性・排他は K2 でも同様に通るので、決め手は義務の形と行の局所性。最終 carrier の決定は reviewer。

### 3. Lean（`Tools/ShippingGen5ConstValueEKey.lean`、既存ファイルは書き換えていない）

- `PrimTableK := { tys tms : Name → List Level → Option Row }`、`TDenK` / `ArgsDenK` / `CVEK`（`CVE` の写し。`prim`/`tcon` の lookup だけ `c ls`）。
- 定理: `tdenk_fun` / `argsdenk_fun` / `cvek_fun`（`∀ PT env`、前提は二つの導出だけ）、`constValueEKAt_functional`、`CVLSK PT : ConstValueRel`。
- 橋: `cve_toK`（`CVE PT … → CVEK PT.toK …`）、`PrimTableK.ofPoly`、`OblRowTypedK`（型だけ。仮定も証明もしていない）。
- 不変: `Dyn`（`Type 0`）、`TyRow`/`TmRow`、規則、排他条件、`LS`。

### 4. Check（`Tests/Gen5/KeyCheck.lean`）

- 型の構造照合: `CVLSK PT : ConstValueRel`、`ConstValueFunctional (CVLSK PT)`、`cvek_fun` / `tdenk_fun` の型、`cve_toK`。
- 13 名の一部（`Bool.rec`: `[0]`/`[1]`、`Nat.rec`: `[1]`/`[2]`）について、異なる ls の 2 つの row が衝突せずに表せる（`TK_two_rows`、`TK_two_rows_nat`）。
- 負対照: `Name` だけの key では 2 つの row が衝突する（`nameKey_collides`、`TK_not_nameKeyed`、`toK_level_blind`）。
- 実環境で `Bool.rec` / `Nat.rec` / `List.rec` / `PProd.mk` / `PUnit.unit` / `False.rec` の宣言された型が `[0]` と `[1]` で異なる（meta）。
- `#print axioms`: 関数性・橋は propext / Classical.choice / Quot.sound のみ。表の例は propext のみ。sorryAx なし。

### 5. 全コーパスでの残余（新しい key、`Tests/Gen5/PrimResidueKey*.lean`、meta）

測定は 5 つの driver の合算。`MemNameCollision{Design,GateDesign,GateTypedAll,Gen}Test` は推移 import の `MemNameCollisionCertTest` などと環境が衝突して同時に import できないので、1 module ずつ別 driver（`PrimResidueKeyM1..M4`）で測り、残り 43 module は `PrimResidueKey`（main43）で測った。共通部は `PrimResidueKeyLib`、合算は `scripts/gen5/merge_prim_residue_key.py`（raw の key 行と root 行を和集合にする）。

count 行（merge の出力）: `235 distinct root names (237 (root, module) pairs: 199 source, 38 sound-only), 47/47 modules with roots`。
root = `X.machine_source` を持つ定義 X（194 + 隔離 module 由来 5）に、`machine_source` を作らない枝（`_of_regs` / `_of_comb` / surface）の `X.machine_sound` だけを持つ X（38）を加えた。前回は後者を数えず、4 module（ApplicativeSemantics / DepthRegsChild / ShippingMachineComb / ShippingSignOps）は root が 0 だった。今回は 47 module すべてに root がある。

**fuel の検査**: `reach` は fuel 回 pop した時点で止まる。worklist が残った root が 1 つでもあれば `throwError`（残った todo の件数と root を出す）。5 driver とも fuel=400000 で全 root が完走（残りなし）。負対照 `#prim_residue_key_neg 50`: 232 root 中 229 が失敗し、検査が通ることを確認（通ったら build が失敗する）。
前回の「完走」は誤りだった: 旧実装は worklist に push するとき seen を見ず、`Keccak256Sponge.keccak256SpongeHW`（残り 1252014）と `wKeccakF`（残り 640515）の 2 root が fuel を使い切り、残りを捨てて部分結果を返していた。fuel を上げず、push 時に seen を印す形に直した（到達集合は同じ。distinct な `(name, ls)` ごとに 1 回だけ push するので worklist は有限）。これで 2 root も完走し、`induct` が 1 名増えた。

| 項目 | 数 |
|---|---|
| module | **47/47**（main43 + M1..M4。各 driver が推移 import で入れる 2 module を除く） |
| root（distinct name / (root, module) 組） | 235 / 237（`machine_source` 199、`machine_sound` のみ 38） |
| 残余の行数、Name-only key（= K2 level-polymorphic も同数） | 191 |
| 残余の行数、`Name × List Level`（K1） | **204**（追加 13 行。旧: 188 / 201） |
| 内訳（name / (name, ls)）: コンストラクタ | 95 / 100 |
| 再帰子 | 11 / 15 |
| 型の基本形（induct） | 85 / 89 |
| quot / axiom / opaque | 0 / 0 / 0 |
| 複数の ls で現れる名前（Name だけの key で衝突） | 11 / 191（3 種: `PProd`, `PProd.mk`。2 種: `Bool.rec`, `False.rec`, `Nat.rec`, `List`, `List.cons`, `List.nil`, `List.rec`, `PUnit`, `PUnit.unit`） |
| level が閉じていない key | 0 |

- Name だけの key との違い: 同じ 11 名が複数の `ls` で現れ、Name-only は 11 名を 1 行ずつしか持てない。K1 は 13 行多い（(name, ls) の組を別行）。K2 は 191 行のまま。
- 追加 13 行は前回と同じ 13、種類は ctor 5・rec 4・induct 4。
- 生データ（key 行と root 行）は `KJOB_REPORT_PATH`（`report.md.key.*`、`report.md.roots.*`、集計は `report.md`）。ソースツリーには置いていない。
- 限界: 証明項を数えない近似。`Type 0` の `Dyn` に収まらない key（例 `Bool.rec` の motive が `Sort 2` 以上）が何件かは未測定。健全性（`OblRowTypedK`）は未証明・未仮定。


### 6. 主張しないこと

最終 carrier の決定、健全性、TRUSTED の要否。台帳の数は変わらない（FG 75 / T1 57、今回 FG -0 +0 / T1 -0 +0）。

## §Sound: 規則の健全性（Issue `sparkle-ledger-dd4-sound`、土台 66b2aada）

reviewer の方針: K1 の key、LS env X、level 固定の関数性は承認済み。最終 carrier、規則の健全性、`OblRowTypedK`、G-PRIM/TRUSTED は未承認。`OblLevelErase` は仮定にも axiom にもしない。TRUSTED・axiom・sorry・native_decide なし。`PT` は任意のパラメータ。既存ファイルは書き換えていない。
新ファイル: `Tools/ShippingGen5ConstValueESoundK.lean`、`Tests/Gen5/SoundKCheck.lean`、`Tests/Gen5/RowTypedKAudit{Lib,,M1..M4}.lean`、`scripts/gen5/merge_row_typed_audit.py`。

### 1. 証明できたもの（`ShippingGen5ConstValueESoundK`、axiom は propext / Classical.choice / Quot.sound のみ）

- **構文だけの `lift` / `subst`**。`Expr.liftLooseBVars` / `Expr.instantiate1` / `Expr.looseBVarRange` は `opaque`（extern）なので、補題が得られない。そこで構造再帰の `liftS` / `substS` / `lbr` を置き、これについて証明した: `liftS_closed`（閉じた式の lift は恒等。`OblLiftClosed` の構文版）、`liftS_zero`、`substS_closed`（閉じた codomain への代入は恒等）、`substS_bvar_lt/eq/gt`、`instForall_nondep_closed`。
- **規則の判定 `TyRK`**（`CVEK` の規則ごとに 1 つ、`natLit/strLit/bvar/const/app/lam/letE/unfold/prim`）と、その上での義務の充足: `OblBvar` / `OblApp` / `OblLam` / `OblConst`（既存）と新設の `OblLit` / `OblLet` / `OblUnfold` / `OblPrimK` が `TyRKJ PT` について**無条件に**成り立つ（`oblBvar_TyRK` 〜 `oblPrimK_TyRK`、束 `kernelRulesK_TyRK`）。意味: 義務の束は充足可能で、空疎ではない（負対照: 何も導かない `Ty` は束を満たさない）。`TyRK` はカーネルの判定ではない。
- **`cvek_tyRK`**: `CVEK PT env ρ e τ α v → TyRK PT env (ρ.map Entry.τ) e τ`。規則ごとの対応は、bvar（`map_getElem?_entry` で `ρ[i]? = some en → (ρ.map τ)[i]? = some en.τ`、型は `en.τ.liftLooseBVars 0 (i+1)`）、lam（文脈の拡張 `⟨A,d⟩ :: ρ` の `map τ` が `A :: ρ.map τ`: `map_cons_entry`。body は `a0` での導出から）、app、letE、unfold、prim。
- **`tyRK_sub` / `cvek_sound`**: 束 `KernelRulesK PT Ty` が成り立つ任意の `Ty` について `TyRK ⊆ Ty`、したがって `CVEK → Ty env (ρ.map τ) e τ`。これは**名前付き Prop 間の含意**で、どこでも仮定として使っていない（reviewer が不要と見るなら削除してよい）。
- **`instForall` と app 規則の対応**: `TyArgs`（引数ごとの型付け）について `instForall T as = R`（`tyArgs_instForall`）、`TyRK` の spine（`tyRK_spine`）。
- **lam の B と TB**: `TDenK` の `pi` 規則から、body の型 `B` が各 `a` で `TB a` を表すなら `∀ a, B` は `(a : TA) → TB a` を表す（`denTyped_lam`、`denTyped_lam_of_body`）。prim は `hty` そのもの、unfold は body の `τ α` をそのまま使うので、`OblDenTyped`（`CVEK ⇒ TDenK τ α`）の lam / prim / unfold の 3 規則は証明できている。
- **`OblRowTypedK` の整理**: key ごとの義務 `RowTypedAt PT env c ls`（`ci`、`row`、`ρ`、`args`、`as`、`d` について `TDenK … (instForall (ci.type.instantiateLevelParams ci.levelParams ls) args) d.ty`）。`oblRowTypedK_iff`（`OblRowTypedK ↔ ∀ c ls, RowTypedAt`）、有限表の場合の `oblRowTypedK_of_keys`、行のない key（`rowTypedAt_of_none`）と `den` が常に `none` の行（`rowTypedAt_of_den_none`: `Type 0` に収まらない key の逃げ道）は義務なし、引数なしの行（`kinds = []`）は「宣言型を `ls` で instantiate したものが `d.ty` を表す」に帰着（`rowTypedAt_nullary`）、`argsDenK_length`（`args.length = kinds.length`）。
- **実際の 1 行の証明**: `Tests/Gen5/SoundKCheck.lean` の `rowTyped_natZero`。`Nat.zero` の行が `RowTypedAt` を満たす。env の事実（`Nat.zero` の `ci.type = Nat`、`levelParams = []`、`Nat` が `defnInfo` でない）は補題の仮定にした（環境についての事実であって `PT` についての仮定ではない）。引数ありの行（`Nat.succ` など）は `instantiate1` が `opaque` なので、閉じた codomain への `instantiate1` の恒等（ブリッジ）が要る。

### 2. 残った義務（名前付き `Prop` の定義。仮定にも axiom にもしていない）

| 義務 | 内容 | 現状 |
|---|---|---|
| `OblLiftAgree` | `e.liftLooseBVars s n = liftS e s n` | `liftLooseBVars` は opaque（extern）。**現在の API と導出では得られず未解決** |
| `OblInst1Agree` | `b.instantiate1 x = substS b 0 x` | 同上（`instantiate1`） |
| `OblLbrZero` | `e.looseBVarRange = 0 → lbr e = 0` | `looseBVarRange` は `Expr.data` の 20 bit 欄。`mkData` が範囲超過で panic する点も含め未解決 |
| `OblLiftClosed`（既存） | 閉じた式の lift は恒等 | 上の 2 つのブリッジに**還元**（`oblLiftClosed_of_bridges`）。構文版は証明済み |
| `OblBvar/OblApp/OblLam/OblConst Ty`（既存、`Ty` はカーネルの型付け） | 各規則 | `TyRK` については証明済み。**カーネルの `Ty` がこれらを満たすこと**は、Lean core に `Prop` の型付け判定がないので述べられない（`Ty` はパラメータのまま） |
| `OblLit` / `OblLet` / `OblUnfold` / `OblPrimK` | 新設。`CVEK` の lit / let / unfold / prim 規則 | 同上。`OblUnfold` は β/δ 同値での型保存、`OblPrimK` は引数の型付け（`ArgsDenK` から各引数が telescope に型付く。型引数は `TDenK` を通すだけで `tcon` に `hty` がない）を含む |
| `OblDenLits` | `Nat` / `String` の `tys` 行がある | `PT` の中身の条件 |
| `OblDenSubst` | `app` / `letE` が行う代入と `TDenK` の可換 | 未解決（`OblInst1Agree` と、`TDenK` の代入補題が要る） |
| `OblDenBvar` | valuation の整合と weakening（bvar） | 未解決（`OblLiftAgree` と weakening が要る） |
| `OblDenTyped` | `CVEK ⇒ TDenK τ α` | lam / prim / unfold は証明済み。残りは上の 3 つ |
| `OblRowTypedK` | 表の行ごと（`RowTypedAt`） | 行ごとの有限・局所な義務。1 行（`Nat.zero`）を証明。他は行ごとに証明する |
| `OblLevelErase` | 仮定にも axiom にもしない（`LS` で迂回） | 既存のとおり未解決 |

`opaque` について: 「原理的に証明不能」とは言わない。「現在の API と導出では得られず未解決」。

### 3. `OblRowTypedK` の行ごとの監査（`Tests/Gen5/RowTypedKAudit*.lean`。**監査であって証明ではない**）

K1 の key 204 件（ctor 100 / rec 15 / induct 89。§Key と同数）について meta で機械的に確かめた（5 driver、`scripts/gen5/merge_row_typed_audit.py` で合算、driver 間で行の不一致 0）。確かめた内容:
- arity: `ls.length = ci.levelParams.length` が **204 / 204**。
- const: `inferType (mkConst c ls)` が `ci.type.instantiateLevelParams ci.levelParams ls` と構文的に一致が **204 / 204**（defeq のみ 0、不一致 0）。
- spine: 宣言型の binder telescope（fresh fvar）のすべての prefix について、`inferType (mkAppN (const c ls) xs[:j])` が `instForall T0 xs[:j]` と構文的に一致が **204 / 204**。
- 負対照: `ls` を `succ` でずらした型と比べると、level 多相の 120 key すべてで不一致（検査が通るだけの検査ではないことの確認）。
- 参考（宣言型の sort、`ls` で instantiate した型の `inferType`）: Prop 9 / Type 0 44 / higher 151。項の key（ctor/rec、115 件）では Prop 9 / Type 0 40 / higher 66。`d.ty : Type` に入るのは `Type 0` の型を持つ key で、higher の key は `row.den` が `none` を返す形で逃げる必要がある（上の `rowTypedAt_of_den_none`）。applied した結果の sort はまだ測っていない。
- **限界**: これは `ConstantInfo.type` と `instForall` が Lean 自身の `inferType` と一致することの確認で、ほぼ自明な側（定数の型は宣言型）。`row.den`、`ArgsDenK`、`TDenK` には触れていないので、`RowTypedAt` の証明にはならない。引数の型付け（`OblPrimK`）も確かめていない。

### 4. 最終 carrier に必要な残り

1. `liftLooseBVars` / `instantiate1` / `looseBVarRange` の構文版との一致（3 つのブリッジ）、またはこれらを使わない構文への carrier の書き換え。
2. カーネルの型付け `Ty` の側: core に `Prop` の判定がないので、(a) `Ty` を `TyRK` のような規則判定として carrier に入れる（この場合 `OblUnfold` / `OblPrimK` が実質の義務）、または (b) 実際のカーネルとの一致を meta の検査で扱う、の選択が要る。reviewer の判断。
3. `OblPrimK`（引数の型付け、とくに型引数）と `OblDenTyped` の残り 3 つ（`OblDenLits` / `OblDenSubst` / `OblDenBvar`）。
4. `OblRowTypedK`: 実際に置く行ごとの証明（K1 の term key 115 件のうち、`Type 0` に収まる 40 件が実質の対象。ほかは `den = none` か Prop）。
5. `OblLevelErase` は引き続き未解決（`LS` による level 固定のまま）。

### 5. Check と台帳

`Tests/Gen5/SoundKCheck.lean`（証明した補題の型の構造照合、負対照、39 宣言の axiom 検査と検出器の負対照、残った義務 20 件の一覧、`#print axioms`）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## §SoundS: 構文版 carrier `CVEKS` と健全性（Issue `sparkle-ledger-dd4-sound`、土台 c9ca68a2）

reviewer の判断 D1 = 案 a（opaque 演算を構文版に置換）、D2 = 案 a（`TyRKS` は carrier 内の構文的な型付け判定）。TRUSTED・axiom・sorry・native_decide なし。`PT` は任意のパラメータ。既存ファイルは書き換えていない。
新ファイル: `Tools/ShippingGen5ConstValueES.lean`（carrier）、`Tools/ShippingGen5ConstValueESProof.lean`（証明）、`Tests/Gen5/SoundSCheck.lean`。P3（行ごとの `RowTypedAt`）は `sparkle-ledger-dd4-rows` の担当で、ここでは触っていない。

### 1. carrier `CVEKS`（`ShippingGen5ConstValueES`）

`CVEK` の規則のうち、`bvar` の型は `liftS en.τ 0 (i+1)`、`app` / `letE` は `substS B 0 x`、`unfold` は `betaS`（構造再帰、新規定義）、`prim` の型は `instForallS`（`substS` で定義）にした。`Expr.beta` / `Expr.instantiate1` / `Expr.liftLooseBVars` は carrier に現れない。
`cveks_fun`（`tdens_fun` / `argsdens_fun` を含む）は `cvek_fun` の証明がそのまま通った（`spine_inj` / 排他条件 `hnh` / `IsDefn` は同じ）。`ConstValueEAtS`、`CVLSKS`（`LS` env の固定レベル）に対して関数性 `constValueEAtS_functional` / `cvlsks_functional`。
carrier に残る Lean の `Expr` API は `Expr.instantiateLevelParams`（unfold の本体と prim の宣言型）、`Expr.getAppFn`（構造的）、`env.find?`。`instantiateLevelParams` は構文版に置換していない（§3 の `EnvClosedS`）。

### 2. 証明したもの（axiom は propext / Classical.choice / Quot.sound のみ。`SoundSCheck` で 48 宣言を検査）

- **構文演算の補題**: `liftS_liftS_le/add`、`liftS_substS`、`substS_liftS_in/ge`、`substS_substS`（2 回の代入の可換）、`liftS_betaS` / `liftS_instForallS` / `liftS_mkAppN`、`substS_betaS` / `substS_instForallS` / `substS_mkAppN`、`getAppFn_liftS` / `getAppFn_substS`。
- **弱化**（`tdens_wk` / `argsdens_wk` / `cveks_wk`）: 位置 `s` に 1 つ挿入した valuation（`InsV`）について、導出が `liftS … s 1` に写る。全規則（`pi/tcon/tunfold`、`natLit … prim`）。
- **P1 `OblDenBvar`**: valuation の整合性 `WfValS`（各 entry の型が、その valuation で `en.d.ty` を表す）の下で `oblDenBvarS`。`wfValS_cons`（弱化を使う）で binder を足しても整合性が保たれる。**任意の valuation では成り立たない**（entry の `τ` が無関係な式なら表す型がない）ので、主張は `WfValS` 付き。ルートの `ρ = []` は整合（`wfValS_nil`）。
- **P1 `OblDenLits`**: 行の形の補題 `oblDenLits_of_rows`（`Nat` / `String` の nullary な `tys` 行と `¬IsDefn` が前提）。`PT` の中身の条件なので、行があるときだけの補題。
- **P1 `OblDenSubst`**: 代入補題 `tdens_subst` / `argsdens_subst` / `cveks_subst`（valuation の関係 `SubV`、全規則）と、`oblDenSubstS_safe`（`SafeArg x` のとき）。**一般の x では未証明**（§3）。
- **`OblDenTyped`（`CVEKS ⇒ TDenS τ α`）**: `denTypedS` が 8 規則すべてを閉じる。前提は名前付きの 3 つ（`Nat`/`String` の行、`EnvClosedS`、`OblDenSubstS`）。`natLit`/`strLit` は行、`bvar` は `WfValS`、`lam` は `wfValS_cons` と `.pi`、`unfold` は本体、`prim` は `hty`、`app`/`letE` は `OblDenSubstS`。
- **P2 `TyRKS`**（`TyRK` の構文版）: `natLit/strLit/bvar/const/app/lam/letE/unfold/prim`。`prim` は強い形（引数を宣言型の telescope に対して型付ける `TyArgsS`）。`OblBvarS/OblAppS/OblLetS/OblUnfoldS/OblPrimKS` と束 `KernelRulesKS`。`kernelRulesKS_TyRKS`（束は `TyRKSJ` で充足可能）、`tyRKS_sub` / `tyArgsS_sub`、`cveks_tyRKS`、`cveks_sound`（前提 `OblPrimArgsS`）。`OblUnfoldS`（β/δ での型保存）は `TyRKS` の `unfold` 規則そのもの。**カーネルの型付けとの一致は主張しない**。

### 3. 最終 carrier に残るもの（名前付き `Prop`。仮定にも axiom にもしていない）

| 残り | 内容 | 理由 |
|---|---|---|
| `OblDenSubstS`（一般の x） | `app` / `letE` が行う代入と `TDenS` の可換 | 証明は `SafeArg x`（`lam` でも `forallE` でも const 頭でもない）に限る。(a) `x` が const 頭のとき、置換後の `bvar k y` は const 頭の spine になり、`app` 規則の排他条件 `hnh` が禁じる（その spine は `prim` / `unfold` の全 spine でしか導出できず、行の arity が合わなければ導出が存在しない）。(b) `x` が `lam` のとき `substS` と `betaS` が可換でない、`forallE` のとき `instForallS` と可換でない（負対照 `substS_betaS_needs_nonlam` / `substS_instForallS_needs_nonforall`）。すなわち、現在の排他条件と構文 β の下で、一般の代入補題は偽になりうる（反例の形は上記。具体の `PT` での導出の反例までは構成していない） |
| `EnvClosedS` | 環境の宣言型・定義本体が `instantiateLevelParams` 後も閉じている（`lbr = 0`） | `instantiateLevelParams` は `Expr` API の関数（`replace`）で、`lbr` を保つ補題を置いていない。unfold / prim の弱化・代入に必要 |
| `OblDenLits` の行 | `Nat` / `String` の nullary な `tys` 行 | `PT` の中身。`oblDenLits_of_rows` はその行があるときの補題 |
| `RowArgsAt` / `OblPrimArgsS` | prim の引数が宣言型の telescope に型付く（型引数を含む） | `ArgsDenS` からは出ない。項引数の導出ラベル `τ` が telescope の binder 型と構文的に一致する保証がなく（型変換規則を持たない）、型引数は `TDenS`（表す型）しか持たず型付けの根拠がない。nullary の行は `rowArgsAt_nullary` で義務なし。行ごとの有限・局所な義務 |
| `OblRowTypedS`（S 版の行型付け） | `RowTypedAt` の `ArgsDenS` / `TDenS` / `instForallS` 版 | P3（`sparkle-ledger-dd4-rows`）の担当。このブランチでは定義していない |
| カーネルの `Ty` | `KernelRulesKS Ty` が実際のカーネルで成り立つこと | core に `Prop` の判定がなく述べられない。`TyRKS` は carrier 内の構文判定でカーネルと一致を主張しない |

`OblLevelErase` は最終 carrier を固定 LS env の `CVLSKS` / `ConstValueEAtS` に統一すれば不要。**主張は各 root の zero-level instance（`LS env X`）に限る**。全 universe instance への一般化はしない。`∃ ls` の `ConstValueE` を残す場合は `OblLevelErase` の橋が要る。

### 4. 旧 opaque 版との違い（`SoundSCheck` の負対照）

- 旧: `bvar_type_closed` は `OblLiftClosed`（opaque `liftLooseBVars`）を仮説に取る。新: `liftS_closed` は `lbr = 0` だけ。elaborator の `isDefEq` で `Expr.instantiate1 (.bvar 0) c` は `c` と等しいと示せず（stuck）、`substS (.bvar 0) 0 c` は計算できる。
- `SafeArg` の必要性（上の負対照 2 件）、`liftS` / `substS` が恒等でないこと、何も導かない `Ty` が束 `KernelRulesKS` を満たさないこと。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。
## §Rows: 行ごとの `RowTypedAt`（Issue `sparkle-ledger-dd4-rows`、土台 c9ca68a2）

reviewer の方針: 健全性の完了は差し戻し。D1（opaque な演算とのブリッジ）と D2（カーネルの `Ty` の意味）は設計判断待ち。TRUSTED・axiom・sorry・native_decide なし。`PT` は任意のパラメータのまま。既存ファイルは書き換えていない。
新ファイル: `Tools/ShippingGen5RowTypedK.lean`、`Tests/Gen5/RowTypedKCheck.lean`。`Tests/Gen5/RowTypedKAuditLib.lean` に列を 2 つ（shape、型の文字列）足し、`scripts/gen5/merge_row_typed_audit.py` に分類を足した。

### 1. K1 の term key 115 件の分類（meta。`RowTypedKAudit*` の 5 driver を合算、driver 間の不一致 0）

| 分類 | 件数 | 扱い |
|---|---|---|
| `Type 0`、引数なし | 6 | **証明した**（下の 2） |
| `Type 0`、引数あり、codomain が閉じている | 4 | D1 待ち。案 (a) の証明の形は書いた（下の 3） |
| `Type 0`、依存型（codomain が引数を使う） | 30 | D1 待ち（さらに `OblDenSubst`） |
| `den = none` で逃げる key（宣言型の sort が `Type 1` 以上） | 66 | `rowTypedAt_of_den_none`（行が `den = none` という PT の仕様のとき義務なし） |
| Prop（宣言型が Prop） | 9 | 同上 |

合計 6 + 4 + 30 + 66 + 9 = 115。`Type 0` は 40 件（6 + 4 + 30）で、§Sound §3 の数と一致。
- 引数なし 6: `Nat.zero`、`Bool.false`、`Bool.true`、`PUnit.unit.{1}`、`ActiveEdge.rising`、`ResetKind.synchronous`。
- 閉じた codomain 4: `Nat.succ`、`Int.ofNat`、`Int.negSucc`、`DomainConfig.mk`（3 引数）。
- 依存型 30: `Fin.mk`、`BitVec.ofFin`、`Decidable.isTrue/isFalse`（型引数や命題引数に依存）と、`{dom : DomainConfig}` を取る出力 structure の `*.mk` 26 件（フィールドが `Signal dom _`）。
- 「依存」は、binder の変数が後ろの binder の型または結果型に現れること（fvar で判定）。`PUnit.unit.{2}` は higher の 1 件に入る（`PUnit.{2} : Type 1`）。

### 2. 引数なしの行（ブリッジ不要、`RowTypedAt` を証明）

`rowTypedAt_nullary_const`: 行が `kinds = []` で、宣言型を `ls` で instantiate したものが閉じた定数 `.const D Ls` のとき、`RowTypedAt`。使う前提は 3 組。
- `TmSpec PT c ls [] T`: この key の行が `kinds = []` で、`den` の値の型は常に `T`（PT の行の仕様。PT は任意のまま、行の仕様を前提にする）。
- `TyConSpec PT D Ls T`: 型 `D` の `tys` の行が引数なしで `T` を表す（`tcon` 規則に使う）。
- env の事実: `EnvType env c ls (.const D Ls)`（宣言型の instantiate 結果）と `¬ IsDefn env D`。`rowTyped_natZero` と同様に補題の仮定にした。

6 key それぞれの定理は `rowTyped_Nat_zero` など 6 件（Tools）。各 1 行で、補題に仮定を渡すだけ。実際の env でこの仮定が成り立つことは `RowTypedKCheck` の meta 検査（10 key の `EnvType`/`EnvClosedPi` と、型が `defnInfo` でないこと）で示す。生成器は使わず、手書き。

**限界（正直に）**: 実際の `PT`（行の中身）はこのリポジトリにない。したがって「実際の PT の行がこの仕様を満たすこと」は未確認で、Check では仕様を満たす模型の表 `PTm` でだけ補題を使っている（仕様が充足可能で、定理が空疎でないことの確認）。D1/D2 とは独立に、本物の PT ができたときに、行ごとに `TmSpec`/`TyConSpec` の証明が要る。

### 3. ブリッジ待ち（D1）の行 34 件と、案 (a) の証明の形

`instForall` は `Expr.instantiate1`（opaque）で書かれているので、引数ありの行は、`instantiate1` の結果が分からないと `TDenK` の対象の式が決まらない。
- D1 が案 (a)（構文的な `liftS`/`substS` に書き換える）のとき、引数あり・閉じた codomain の行は次の形で閉じる。`instForallS`（`substS` 版）と、それを使う `RowTypedAtS`。`ClosedPi T n R`（`n` 個の binder で、各 body が閉じていて、結果が `R`）のとき `instForallS T args = R`（`instForallS_closedPi`、`substS_closed` を使う）。続いて `rowTypedAtS_closedPi` が、`kinds.length` を binder 数として `RowTypedAtS` を与える。4 key（上の表の 2 行目）の定理が `rowTypedS_Nat_succ`、`rowTypedS_Int_ofNat`、`rowTypedS_Int_negSucc`、`rowTypedS_DomainConfig_mk`。**これは `instForallS` についての定理で、`RowTypedAt` ではない。**
- `RowTypedAt` に戻す道は `rowTypedAt_of_S : OblInst1Agree → RowTypedAtS → RowTypedAt`（`instForallS_eq` 経由）。`OblInst1Agree` は名前付きの `Prop` で、どこでも仮定していない。案 (a) は carrier の `RowTypedAt` の定義自体を `instForallS` に変えるので、`rowTypedAt_of_S` は不要になる（定義を変えない案のときの橋）。
- 依存型 30 件は、案 (a) でも閉じない。codomain への代入が実際に起こるので、(i) `substS` の具体的な結果と、(ii) `TDenK` の代入補題（`OblDenSubst`）の両方が要る。ここは証明していない。
- 案 (a) 以外のとき（`instantiate1` との一致を別の道で示す、など）は、4 key の定理の形はそのまま使えて、`OblInst1Agree` に相当する橋だけが変わる。

### 4. Check（`Tests/Gen5/RowTypedKCheck.lean`）

- 証明した行（`RowTypedAt`）**6**、ブリッジ待ち **34**（うち案 (a) の形を証明したもの 4、依存型 30）、`den = none` と Prop **75**。合計 115。
- env の事実の meta 検査: 10 key で `EnvType`/`EnvClosedPi` と `¬ IsDefn` が実環境で成り立つ。
- 負対照: (a) 誤った型の仕様は充足できない（`Bool` の行は `Unit` を表さない）、(b) 依存した codomain は `ClosedPi` でない、(c) `instForallS` は依存した codomain では代入を行い、閉じた codomain では行わない、(d) `Fin.mk`・`Decidable.isTrue`（依存）、誤った結果型、`defnInfo`（`Nat.add`）は meta の検査で弾かれる、(e) axiom 検出器は fresh axiom を検出する。
- `#print axioms`: 証明した 21 宣言は propext / Classical.choice / Quot.sound のみ。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

### 5. 主張しないこと

- `OblRowTypedK` の完了。34 件が D1 待ち、75 件が PT の仕様（`den = none`）待ちで、証明した 6 件も仕様と env の事実を仮定している。
- 実際の `PT` の行が仕様を満たすこと。D1 / D2 の決定。引数の型付け（`OblPrimK`）。

## §SoundS2: 構文版の level 代入 `instantiateLevelParamsS` と 4 行の `OblRowTypedS`（Issue `sparkle-ledger-dd4-sound`、土台 7c05d998）

reviewer の部分受理（P1/P2 は D1a/D2a に沿う。`TyRKS` は構文的判定で、kernel typing との一致を意味しない）の続き。TRUSTED・axiom・sorry・native_decide なし。`PT` は任意のパラメータのまま。既存ファイルは書き換えていない。
新ファイル: `Tools/ShippingGen5ConstValueESL.lean`、`Tools/ShippingGen5RowTypedS.lean`、`Tests/Gen5/SoundS2Check.lean`。Q1（`OblDenSubstS` の一般形）と Q2（`RowArgsAt` の型変換）は reviewer 相談中で、ここでは触っていない。

### 1. `EnvClosedS` と `instantiateLevelParamsS`（`ShippingGen5ConstValueESL`）

- `instantiateLevelParamsS ps ls : Expr → Expr`（`Level` は `instLevelS`、`Expr` は構造再帰。`sort` / `const` の level を置換し、他は全 constructor を再帰）。**Lean の opaque な `Expr.instantiateLevelParams` との一致は主張しない**（`SoundS2Check` の負対照: 後者はエラボレータで stuck、前者は計算できる）。
- carrier `CVEKL`: `CVEKS` の `unfold` の本体と `prim` の宣言型の `instantiateLevelParams` だけを `instantiateLevelParamsS` に替えた複製。`tdenl_fun` / `argsdenl_fun` / `cvekl_fun`（証明は `cveks_fun` と同じ形でそのまま通った）、`constValueEAtL_functional`、`cvlskl_functional`。
- **`EnvClosedS` が構文版の上で要求するもの**: `EnvClosedL`（宣言型・定義本体が、どの level 列で instantiate しても `lbr = 0`）。`lbr_instantiateLevelParamsS`（level 置換は `lbr` を変えない）を証明したので、`EnvClosedL` は素の宣言の閉性 `EnvDeclClosed`（保存された `ci.type` / `d.value` の `lbr = 0`）と同値（`envClosedL_of_declClosed` / `envDeclClosed_of_closedL`）。**instantiate の橋は消え、残るのは環境の宣言が閉じているという env の事実だけ**。
- 残るもの: (i) `EnvDeclClosed` は env についての名前付き `Prop`（仮定にも axiom にもしていない。kernel が受理した宣言の性質）。(ii) `ESProof` の補題群（弱化・代入・`denTypedS`）は `CVEKS` の上で `EnvClosedS`（Lean の instantiate）を仮定する形のまま。`CVEKL` への移植（`EnvClosedL` を仮定する版）は機械的だが、このブランチではしていない。`CVEKL` では関数性のみを証明した。

### 2. `OblRowTypedS`（`ShippingGen5RowTypedS`）

- `RowTypedAtES PT env c ls`: `RowTypedAt` の S 版（`ArgsDenS` / `TDenS` / `instForallS`）。`OblRowTypedS PT env := ∀ c ls, RowTypedAtES PT env c ls`。`instantiate1` / `liftLooseBVars` / `OblInst1Agree` は現れない。`rowTypedAtES_of_none` / `_of_den_none` / `oblRowTypedS_of_keys`（有限表の分解）。
- **codomain が閉じた 4 行を証明**: `rowTypedES_Nat_succ` / `_Int_ofNat` / `_Int_negSucc` / `_DomainConfig_mk`。道具は `instForallS_closedPi`（`substS_closed`）と `argsdens_length`、行の仕様 `TmSpec` / `TyConSpec`（`PT` は任意、仕様を前提にする）、env の事実 `EnvClosedPi` / `¬ IsDefn`（実環境では `RowTypedKCheck` の meta 検査で確認済み）。

### 3. 残った義務の一覧

| 残り | 状態 |
|---|---|
| `OblRowTypedS` の依存した codomain 30 件（`Fin.mk`、`BitVec.ofFin`、`Decidable.isTrue/isFalse`、`{dom : DomainConfig}` を取る出力 structure の `*.mk` 26 件） | **Q1 待ち**。`substS` の具体的な結果と `OblDenSubstS` の一般形が要る。名前の全件は `merge_row_typed_audit.py` の最終行（コーパス監査、ここでは再計算しない） |
| `OblRowTypedS` の `den = none` / Prop 75 件、引数なし 6 件 | `rowTypedAtES_of_den_none`（行が `den = none` という `PT` の仕様のとき）／`RowTypedAt` で既に証明（S 版の引数なし 6 件は `ArgsDenS` の長さ 0 で同様に閉じるが、ここでは定理にしていない） |
| `OblDenSubstS` の一般形 | Q1 待ち（変更なし） |
| `RowArgsAt` / `OblPrimArgsS` | Q2 待ち（変更なし） |
| `EnvDeclClosed` | env の事実（名前付き `Prop`、未仮定） |
| `ESProof` の `CVEKL` への移植 | 未着手（機械的） |

### 4. Check（`Tests/Gen5/SoundS2Check.lean`）

構造照合（`instantiateLevelParamsS` の定義の展開、`cvekl_fun` ほかの形、`lbr_instantiateLevelParamsS`、`EnvClosedL ↔ EnvDeclClosed`、4 行の定理をモデル表 `PTm` で具体化）、負対照（instantiate が恒等でなく param 名を区別する、opaque 版は stuck・構文版は計算できる、依存した codomain と arity 違いは `ClosedPi` でない、誤った型の仕様はない、axiom 検出器の検出）、`#print axioms` と 24 宣言の axiom 検査（propext / Classical.choice / Quot.sound のみ）、残った義務 8 件が定理でも axiom でもなく `Prop` の定義であることの確認、115 件の区分（4 + 30 + 6 + 75）。
## §Val: valuation carrier `CVEKV` と証拠つきの型変換（Issue `sparkle-ledger-dd4-val`、土台 7c05d998）

reviewer の判断 Q1 = (a)、Q2 = (a)。TRUSTED・axiom・sorry・native_decide なし。`PT` は任意のパラメータ。`TyRKS` は kernel typing との一致を主張しない。既存ファイルは書き換えていない（lakefile と草案は末尾追記のみ）。
新ファイル: `Tools/ShippingGen5ConstValueEV.lean`（carrier と証明）、`Tests/Gen5/ValCheck.lean`。土台は `kjob lake build Tests.Gen5.SoundSCheck` で通ることを先に確認した。

### 1. carrier（Q1: valuation 経由、Q2: 証拠つきの変換）

- `CVEKVB`（規則）: `CVEKS` の規則のうち `app` / `letE` を変えた。引数を `CVEKV` で先に意味へ評価して valuation に積む。結果の型ラベルは構文代入ではなく **`letE` ラベル**:
  `app` は `.letE n A x B false`、`letE` は `.letE n A v B nd`。それを表す規則 `TDenV.tlet`（`x` を評価して valuation を伸ばし、`B` を表す）を足した。`substS` は `app` / `letE` / `tlet` の型に現れない。
- `CVEKV`（外から見る導出）: `core`（規則そのまま）か、`conv`（規則の導出 1 つの型ラベルを `τ0 → τ` に替える）。**`conv` は `TDenV ρ τ0 α` と `TDenV ρ τ α` の両方（同じ Lean 型 `α` を表す証拠）がある場合だけ**。無条件ではない。`cvekv_conv` で 1 段にまとめられる。
- `conv` を許す位置と許さない位置。許す: 引数（`ArgsDenV.tm`、`app` の `hx`、`letE` の `hv`）とルート。許さない（`CVEKVB` を持つ）: `app` の関数、`lam` / `letE` の本体、`unfold` の本体。
  理由: `lam` の本体のラベルを替えたいなら `lam` 全体を `conv` すればよい（`pi` 規則で同じ証拠になる）ので表現力は落ちない。**関数位置**でラベルを `forallE A B` に替えると、同じ `Π` の分解 `(A, B)` が複数でき、結果型 `TB av` の一意性に `Π` の単射性（`((a:TA)→TB a) = ((a:TA')→TB' a) → …`）が要る。Lean で証明できないので、関数位置はラベルを一意にする（規則だけ）。
  `ValCheck` の対照 6 に、同じ `Nat → Nat` を表す異なる 2 つの `Π` ラベルを置いた。
- `prim` / `unfold` は `CVEKS` と同じ（`instForallS` / `betaS` はラベルの構文演算として残る。`hty` は P3 の `OblRowTypedS` の形のまま）。root は `ConstValueEAtV` / `CVLSKV`（`CVLSKS` と同じ `LS env X`、`ρ = []`、`const X ls`）。

### 2. 証明したもの（axiom は propext / Classical.choice / Quot.sound のみ。`ValCheck` で 29 宣言を検査）

- **関数性（変換を含む同時帰納）**: `tdenv_fun` / `argsdenv_fun` / `cvekv_fun` / `cvekvb_fun`、`constValueEAtV_functional`、`cvlskv_functional`。`cvekvb_fun` は規則だけの導出でラベルまで一意（`τ = τ' ∧ α = β ∧ HEq v w`）。`cvekv_fun` は `conv` があっても**値と Lean 型が一意**（`α = β ∧ HEq v w`。ラベルは一意でない）。`CVEKS` の証明がほぼそのまま通った（`conv` は外側 1 段だけなので、構造再帰が通る）。
- **弱化**: `tdenv_wk` / `argsdenv_wk` / `cvekv_wk` / `cvekvb_wk`（`tlet` と `conv` を含む全規則。`EnvClosedS` は `CVEKS` と同じ名前付きの前提）。
- **soundness `denTypedV`（`CVEKV ⇒ TDenV τ α`）**: 全規則と `conv` を閉じた。前提は `EnvClosedS`（弱化に使う）、`Nat` / `String` の行（`OblDenLits`、`PT` の条件）、valuation の整合 `WfValV` だけ。**`OblDenSubstS` は前提にも証明の中にも出ない**（`app` は `tlet hA hx (hB av)`、`letE` は `tlet hA hv (本体の soundness)`、`conv` は証拠 `h1`）。`ValCheck` が `denTypedV` から届く宣言を meta で数え、`OblDenSubstS` / `tdens_subst` / `SafeArg` などが含まれないこと、`CVEKVB.app` / `letE` / `TDenV.tlet` / `CVEKV.conv` の型に `substS` が出ないことを確かめる（検出器の対照: 旧 `denTypedS` は `OblDenSubstS` に届く、旧 `CVEKS.app` / `letE` は `substS` を含む）。
- **`RowArgsAt` / `OblPrimArgsS` を変換規則で供給できる範囲**: `ArgsTeleV`（引数を telescope に対して、変換後のラベルで型付ける）と、行が出す証拠 `TeleEv`。
  - **項引数**: binder 型が引数の Lean 型を表す（`TeleEv.tm` は `TDenV` の証拠）なら、`conv` で引数のラベルを binder 型にできる。引数自身のラベルの証拠は `denTypedV` が出すので、生産者は要らない（`argsTeleV_of_ev`。`WfValV` 付き）。
  - **型引数**: carrier の中では型付けされない（`TyRKS` に `forallE` / `sort` の規則がない。`tyRKS_no_forallE`）。telescope 側の binder が `sort` であること（種類の検査、`TeleEv.ty`）だけを求める。型引数に対する型付けの根拠は `TDenV`（表す型）のみ。
  - 結論 `rowArgsAtV_of_ev` / `oblPrimArgsV_of_ev`: 行ごとの `RowTeleEvAt`（証拠）から `RowArgsAtV` が出る。nullary の行と、`tms` に行がない key は証拠なし（`rowTeleEvAt_nullary` / `rowTeleEvAt_of_none`）。

### 3. 負対照（`Tests/Gen5/ValCheck.lean`）

- 正の例: 模型の表 `PTv`（`Nat ↦ Nat`、別名 `Tst.M ↦ Nat`、`Tst.U ↦ Unit`）で、`lit 0 : Nat` を別名ラベル `Tst.M` に `conv` できる（両方の証拠がある）。
- **証拠なしの変換は壊れる**: `Tst.U`（`Unit` を表す）は `Nat` を表さない（`tden_U_not_Nat`）。ゆえに `lit 0` を `Tst.U` に替えようとしても `conv` の `h1` が作れない。無条件の変換なら `OblDenTyped` の結論が任意のラベルで成り立つはずだが、それは偽（`uncond_conv_unsound`）。型の不一致（`Unit` と `Nat` は 1 点と無限）が具体的な反例。
- `WfValV` は本当の前提（`not_wfValV_junk`）、`TeleEv` も本当の前提（`teleEv_mismatch`: `Nat` の引数を `Tst.U` の binder に当てられない）。
- 無条件の変換が**関数性**を壊すかは、関数位置を `CVEKVB` に限ったため、この carrier では起きない。関数位置を許すと `Π` の単射性が要る（上の理由）。これは具体的な反例ではなく、証明できない仮定の指摘である。

### 4. 残った義務（名前付き `Prop`。仮定にも axiom にもしていない）

| 残り | 内容 |
|---|---|
| `EnvClosedS` | 環境の宣言型・本体が `instantiateLevelParams` 後も閉じている。別 Issue（`instantiateLevelParams`）が担当。弱化と soundness の `bvar` が使う |
| `Nat` / `String` の行 | `OblDenLits`。`PT` の中身の条件 |
| `RowTeleEvAt`（行ごと） | 項引数の binder 型が引数の Lean 型を表すという証拠、型引数の binder が `sort`。`ArgsDenV` からは出ない。行ごとの有限・局所な義務 |
| `OblRowTypedS` | 行の `hty`（`prim` の `hty` と同じ形）。P3 / 別 Issue |
| カーネルの `Ty` | `TyRKS` は carrier 内の構文判定。kernel typing との一致は主張しない。core に `Prop` の判定がなく述べられない |

### 5. 主張しないこと

- 旧 carrier `CVEKS` の導出から `CVEKV` の導出への写像は作っていない。`lam` の本体のラベルを全 `a` で共通にする必要があり、旧導出の形（`a` ごとに異なりうる）から共通のラベルを選べない。比較は規則のレベルで述べた（値と Lean 型は同じ規則、違いは `app` / `letE` のラベルと `conv`）。
- 全 universe instance への一般化（`OblLevelErase`）。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## §V2: `CVEKVL`、literal の行、`RowTypedAtV` / `RowTeleEvAt`、旧 `CVEKS` との関係（Issue `sparkle-ledger-dd4-v2`、土台 10112fb6）

reviewer: CVEKV は承認済み。範囲外だった残り（`EnvClosedS`、literal の行、`RowTeleEvAt` / `OblRowTypedS`、旧 `CVEKS` との写像）を扱う。kernel `Ty` との一致は D2a のとおり主張しない。TRUSTED・axiom・sorry・native_decide なし。`PT` は任意のパラメータのまま。既存ファイルは書き換えていない（lakefile と草案は末尾追記のみ）。
新ファイル: `Tools/ShippingGen5ConstValueEVL.lean`、`Tools/ShippingGen5RowTypedV.lean`、`Tests/Gen5/V2Check.lean`。土台は `kjob lake build Tests.Gen5.ValCheck Tests.Gen5.SoundS2Check` が通ることを先に確認した（merge 後そのまま通った）。

### 1. `CVEKVL`: CVEKV の level の構文版、`EnvClosedS` を示した

- `CVEKVL`（`ShippingGen5ConstValueEVL`）は `CVEKV` の複製で、`unfold` の本体と `prim` の宣言型の `Expr.instantiateLevelParams` だけを `instantiateLevelParamsS`（SoundS2）に替えた。`EnvClosedS` は `EnvClosedL` に替わる。`CVEKV` の証明（関数性 `cvekv_fun` / `cvekvb_fun` / `tdenv_fun`、弱化、`denTypedV`、`argsTeleV_of_ev` ほか）が名前の置換だけでそのまま通った。
- **`EnvClosedS` に当たるもの**: `envClosedL_cvekvl : EnvDeclClosed env → EnvClosedL env`（SoundS2 の `envClosedL_of_declClosed`、`lbr_instantiateLevelParamsS` を使う）。`tdenv_wk_decl` / `cvekv_wk_decl` / `wfValV_cons_decl` / `denTypedVL` は前提が `EnvDeclClosed`（保存された宣言型・本体の `lbr = 0`）だけになった。**`instantiateLevelParams` の橋は消えた**。残るのは env の事実 `EnvDeclClosed`（名前付き `Prop`、仮定にも axiom にもしていない。別 Issue `sparkle-ledger-dd4-sound` が実環境で監査している）。
- `Expr.instantiateLevelParams` との一致は主張しない（SoundS2 のとおり）。`V2Check` は `CVEKVB.prim` / `unfold` / `TDenV.tunfold` が `instantiateLevelParamsS` だけを含み、`CVEKV` 側の `prim` は opaque 版を含むことを meta で確かめる。

### 2. literal の行（`oblDenLits` の V 版）

`oblDenLitsV_of_rows`: `Nat` / `String` の nullary な `tys` 行（`kinds = []`、値が `Nat` / `String`、定義でない）があれば、どの valuation でも `TDenV ρ (.const `Nat []) Nat` / `String`。`natLit_typed` / `strLit_typed` は literal の規則のラベルが型付くこと。`denTypedVL_of_rows` は `EnvDeclClosed` と 2 行だけから `OblDenTypedV`（`CVEKVL ⇒ TDenV`）を閉じる。**`PT` の中身の条件はこの 2 行（`PT` の仕様）だけ**。

### 3. `RowTypedAtV`（`hty` の義務）と `RowTeleEvAt`（引数の型付け）

`RowTypedAtV PT env c ls`: `prim` の `hty`（宣言型を `instantiateLevelParamsS` で instantiate し、`instForallS` で引数に適用した式が `d.ty` を表す）。`OblRowTypedV` はその全 key。`instantiate1` / `liftLooseBVars` / `OblInst1Agree` は現れない。

| 分類 | 件数 | 状態 |
|---|---|---|
| 引数なし | 6 | **証明**（`rowTypedAtV_nullary_const`、`rowTypedV_Nat_zero` ほか 6 件） |
| codomain が閉じている | 4 | **証明**（`rowTypedAtV_closedPi`、`rowTypedV_Nat_succ` / `Int_ofNat` / `Int_negSucc` / `DomainConfig_mk`） |
| 依存した codomain | 30 | **形が合うものは証明**（下の 3.1）。`PT` の行の仕様（`FirstArgSpec`）を前提にする |
| `den = none` / Prop | 75 | 行が `den = none` という `PT` の仕様のとき義務なし（`rowTypedAtV_of_den_none`） |

**3.1 依存した codomain**: 宣言型が `n+1` 個の binder（binder の型・本体は何でもよい。`instForallS` は見ない）で、結果が `D (bvar n)`（最初の引数に型構成子 `D` を適用した式）のとき、`instForallS T (a0 :: as) = D a0`（`instForallS_depFirst`。`substS` を実際に計算し、`substS_liftS_in` で持ち上げが相殺することを使う）。`rowTypedAtV_depFirst`: 行の仕様 `FirstArgSpec`（その行の値の型は、`D` の `tys` 行の `den` を最初の引数に適用したもの）と `¬ IsDefn env D`、env の事実 `EnvDepFirst` から `RowTypedAtV`。**`OblDenSubstS` は出ない**。結果の型 `D a0` は `D` の行と、最初の引数自身の `CVEKV` の導出（`ArgsDenV` の先頭）で型付く（`V2Check` が `rowTypedAtV_depFirst` 等から届く宣言を meta で数え、`OblDenSubstS` / `tdens_subst` / `SafeArg` などが含まれないことを確認。検出器の対照: 旧 `denTypedS` は届く）。
- 実環境で形を確認したもの: `Fin.mk`（`Fin (bvar 2)`）、`BitVec.ofFin`、`Decidable.isTrue` / `isFalse`、出力 structure の複製 `KOutM.mk`（`KOutM (bvar n)`）。`instForallS` を実際の型に適用した結果も確認（`Fin.mk [5,3,0] = Fin 5`、`[7,3,0]` なら `Fin 7`: 結果が最初の引数に依存する）。
- `Sparkle` 全体の `DomainConfig` 先頭の constructor は 9 件で、7 件がこの形、残り 2 件（`Signal.mk`、`AsSignal.mk`）は `Signal dom α` のように引数を 2 つ取る型構成子を結果に持ち、この定理の範囲外（corpus の出力 structure ではない）。
- corpus の 26 件（`{dom : DomainConfig}` を取る出力 structure の `*.mk`）の名前は corpus 監査（`merge_row_typed_audit.py`）にあり、ここでは再計算していない。**この Issue で corpus 監査（`RowTypedKAudit` と M1〜M4 の 5 driver、meta、ログはソース外）を再実行し、型の文字列から確認した**: 依存した Type 0 の term key 30 件（`HEq` は型構成子で除く）は、`Fin.mk`・`BitVec.ofFin`・`Decidable.isTrue/isFalse` の 4 件と、`{dom : DomainConfig}` を最初の binder に取る出力 structure の `*.mk` 26 件（`ChkOut` `KeccakFOut` `SpongeOut` `MulOut`×3 `HFTOut` `HttpEmitOut` `HttpRequestParserOut` `TxOut` `PeOut` `KOut`×2+1 `AccOut` `TwoOut` `Out` `Pair` `CntOut` `CountOut` `PulseOut` `Acc16Out`×2 `AccOutD` `AccOutF` `MOut`）で、**全件が結果 `D (bvar n)`（最初の引数に型構成子を適用）の形**。したがって `rowTypedAtV_depFirst` の形は 30 件すべてに当てはまる（env の事実 `EnvDepFirst` は型の文字列で確認。名前ごとの Lean 定理は仕様 `FirstArgSpec` を `PT` から受けるので、`PT` ができたときに行ごとに必要）。

**`RowTeleEvAt`（引数の型付けを行ごとの義務に整理）**: `OblPrimArgsV` は `RowTeleEvAt`（項引数は binder 型が引数の Lean 型を表す、型引数は binder が `sort`）から `rowArgsAtV_of_ev` で出る（CVEKV で証明済み）。項引数は証拠つきの `conv` で binder 型をラベルにでき、引数自身のラベルの証拠は `denTypedV` が出す。ここでは行ごとの義務を次の 2 つの事実に分けた。
- 行の仕様 `ArgsTySpec`（その行が受け付ける引数の Lean 型は `Ts`）。
- binder の定数が各 valuation で `Ts` を表すこと `BindersDen`（`tys` の行なら `tdenv_const_nullary`、alias なら `tdenv_const_unfold`）。
`rowTeleEvAt_constPi`（`teleEv_constPi`）: binder が定数 `bs` で本体が閉じた telescope（`ConstPi`）なら、この 2 つと env の事実 `EnvConstPi` から `RowTeleEvAt`。**証明した行**: 引数なし 6（`rowTeleEvAt_nullary`、CVEKV）、codomain が閉じた 4（`teleEv_Nat_succ` / `Int_ofNat` / `Int_negSucc` / `DomainConfig_mk`）。`DomainConfig.mk` の 3 つ目の binder は `Sparkle.Core.Domain.ResetKind`（`abbrev`、`defnInfo`）なので alias の展開で扱う（`V2Check` が env でこれを確認）。

### 4. 証明できなかった行の一覧と理由

| 残り | 件数 | 理由 |
|---|---|---|
| 依存 30 行の `RowTeleEvAt` | 30 | 後ろの binder の型が前の引数を含む（`Signal dom α` の `dom`、`Fin.mk` の `val < n`、`Decidable.isTrue` の `p`）。`TeleEv.tm` は代入後の binder 型（`substS B 0 a`）の `TDenV` を要求する。(i) `Signal`・`BitVec` などの型構成子の `tys` 行は `PT` の中身で、任意の `PT` からは出ない。(ii) 命題の引数（`val < n`、`p` の証明）は `Dyn`（`ty : Type`）にならず、行の `kinds`（`Bool`）でどう扱うかが `PT` 側の決め事。(iii) 型引数（`α`）は carrier の中で型付けされない（`tyRKS_no_forallE`）。行ごとに `PT` の仕様が要る |
| 依存 30 行の `FirstArgSpec` / `EnvDepFirst` | 30 | 定理は証明済みだが、仕様は `PT` の中身（実際の `PT` はこのリポジトリにない）。26 件の env の事実は corpus の名前で個別に確認が要る |
| 引数なし 6 / 閉じた 4 の仕様 | 10 | `TmSpec` / `TyConSpec` / `ArgsTySpec`（`PT` の仕様）と env の事実。モデル表 `PTm` / `PTs` でだけ充足を示した |
| `den = none` / Prop | 75 | `PT` が `den = none` と仕様を満たすこと |
| `EnvDeclClosed` | 1 | env の事実（実環境の監査は別 Issue） |
| kernel の `Ty` | - | 主張しない（D2a） |

### 5. 旧 `CVEKS` との写像: 導出の写像は作れない。規則の対応は証明した

`CVEKS ⇒ CVEKVL` の導出の写像（`SafeArg` の範囲でも）は**作っていない**。理由:
1. **ラベルが違う**: 旧 `app` / `letE` のラベルは `substS B 0 x`、新しい規則のラベルは `letE n A x B false`（構文として別の式。`V2Check` の具体例）。写像は導出の結論を変えるので「同じラベルの導出」にはならず、`conv` が要る。
2. **`conv` に要る証拠が旧導出から出ない**: `conv` は `TDenV ρ (substS B 0 x) α` の証拠を要求する。これは `OblDenSubstS` の V 版の 1 つの instance そのもの。旧 `tdens_subst` は `SafeArg x` でだけ証明済みだが、`SubV` の仕掛けは `TDenS` 用で、`TDenV` 用の代入補題は作っていない（`TDenV` の `tlet` の本体が valuation を伸ばすため `SubV` の再定義が要る）。
3. **`lam` の本体のラベルが全 `a` で共通**: 旧 `lam` の `hb : ∀ a, CVEKS … body B (TB a) (f a)` は `a` ごとに別の導出でよく、新しい `lam` は `a` ごとの `CVEKVB`（ラベル共通）。新しいラベルを選ぶには「ラベルは valuation の値によらない」補題が要る。これは Lean 型 `TA` が値に依存しうる valuation（`Fin n` を表す `TA` など）同士で 2 つの導出を比べる補題で、`HEq` を伴う同時帰納になる。
**証明したもの（規則の対応）**: `cvekv_app_old_of_new` / `cvekv_letE_old_of_new`: 新しい `app` / `letE` の結論に `hsub : TDenV ρ (substS B 0 x) (TB av)`（1 つの代入 instance）を足せば、旧規則の結論 `CVEKV ρ (app fe x) (substS B 0 x) (TB av) (fv av)` が `conv` で得られる。すなわち旧規則は新規則と代入の事実 1 つから導ける。値と Lean 型は同じ規則で一致する（関数性が両 carrier で成り立つ）。

### 6. Check（`Tests/Gen5/V2Check.lean`）

構造照合（`CVEKVL` が `instantiateLevelParamsS` だけを含む、`RowTypedAtV` の形、`instForallS_depFirst`、規則の対応）、モデル表 `PTm` / `PTd` / `PTs`（仕様が充足可能、per-key の定理が instantiate する）、実環境の事実（引数なし 6 の `EnvTypeL`、閉じた 4 の `EnvClosedPiL` と `EnvConstPi`、依存 5 の `EnvDepFirst`、`instForallS` の計算）、負対照（`Fin.mk` は閉じた Pi でない／別の型構成子や別の binder 数を拒む／`Nat.succ` は依存でない／定義 `Nat.add` を拒む／最後の引数に依存する telescope は形に合わない `piN_last_not_first`／`Unit` を受ける行は `ArgsTySpec [Nat]` を満たさない／`FirstArgSpec` の誤った型構成子と kinds を拒む／axiom 検出器の検出）、代入義務に届かないこと、`#print axioms` と 49 宣言の axiom 検査（propext / Classical.choice / Quot.sound のみ）、残った義務が定理でも axiom でもなく `Prop` の定義であること、件数。

### 7. 主張しないこと

- 実際の `PT` が仕様（`TmSpec` / `FirstArgSpec` / `ArgsTySpec` / `BindersDen`）を満たすこと。kernel `Ty` との一致。
- 依存 30 行の `RowTeleEvAt`。旧 `CVEKS` の導出から `CVEKVL` の導出への写像。
- `Expr.instantiateLevelParams` と `instantiateLevelParamsS` の一致。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## §SoundS3: `EnvDeclClosed` の実環境の監査と、ESProof の `CVEKL` への移植（Issue `sparkle-ledger-dd4-sound`、土台 6ee3a1ae）

reviewer の部分受理（§SoundS2 の範囲: lbr 保存、`EnvClosedL ↔ EnvDeclClosed`、`CVEKL` の関数性、明示条件つき 4 行。Lean の opaque な `instantiateLevelParams` との一致は未証明で主張しない）の続き。TRUSTED・axiom・sorry・native_decide なし。`PT` は任意のパラメータのまま。Q1（valuation 化）/ Q2（型変換規則）は `sparkle-ledger-dd4-val` の担当で、そのファイルには触っていない。既存ファイルは書き換えていない。
新ファイル: `Tools/ShippingGen5ConstValueELProof.lean`、`Tools/ShippingGen5EnvDeclClosed.lean`、`Tests/Gen5/EnvDeclClosedAudit{Lib,,M1..M4}.lean`、`Tests/Gen5/SoundS3Check.lean`。lakefile への lean_lib 登録は最初の commit で 1 回。

### 1. `EnvDeclClosed` の実環境の監査（meta。**監査であって証明ではない**）

`EnvDeclClosed env`（保存された `ci.type` と `defnInfo` の `value` が `lbr = 0`）を、実環境の宣言で評価した。`lbr` は `SoundK.lbr` と同じ節の memo 付き転記 `lbrM`（`Nat` の引き算も同じ）で、Lean 自身の `Expr.looseBVarRange` とも照合した（食い違いも反例として数える）。範囲は 2 つ。
- REACHED: PrimResidueKey と同じ root・同じ traversal（`reach`、`checkFuel`）で到達する宣言。47 modules（`PrimResidueKey` と同じ driver 分割: main43 + M1..M4）。
- ALL: その driver の環境の全 constant（`EnvDeclClosed` そのもの）。

| driver | root | module | REACHED（名前 / env にある / defnInfo / 反例） | ALL（constant / 反例） |
|---|---|---|---|---|
| main43 | 232 | 47（推移 import を含む） | 925 / 925 / 734 / **0** | 256129 / **0** |
| M1 | 46 | 14 | 485 / 485 / 349 / **0** | 238065 / **0** |
| M2 | 46 | 14 | 487 / 487 / 351 / **0** | 238368 / **0** |
| M3 | 49 | 15 | 491 / 491 / 355 / **0** | 239490 / **0** |
| M4 | 47 | 14 | 486 / 486 / 350 / **0** | 238218 / **0** |

count 行: `main43: 232 roots / 47 modules, M1..M4 は各 1 つの MemNameCollision module + 共通 import。REACHED 反例 0（5 driver）、ALL 反例 0（5 driver）、env に無い到達名 0`。反例は 0 件なので列挙は空（反例があれば `COUNTEREXAMPLE name part lbr` の行で全件出る形）。
- **fuel / timeout**: `checkFuel` は全 root の worklist が空になることを確かめ、残れば `throwError`（部分結果は返さない）。timeout（heartbeat）も例外で build が失敗する。負対照: fuel=50 では検査が失敗する（`negative control (fuel) ok`）、検出器は `lbr ≠ 0` の type / value を持つ `ConstantInfo` を弾く（`negative control (detector) ok`: 閉じた宣言 `#[]`、開いた value `#[(value,1)]`、開いた type `#[(type,1)]`）。
- 生データは `KJOB_REPORT_PATH`（`report.md.dcl.*`）。ソースツリーには置いていない。
- **限界**: 到達集合は PrimResidueKey の近似（theorem の中は入らない）。ALL は driver ごとの環境で、47 module の合併環境ではない（衝突する 4 module は別環境）。`lbrM` が `lbr` の転記であること自体は構造照合ではなく読んで確認した（`looseBVarRange` との一致 0 不一致がその独立な傍証）。

### 2. 証明として言えること（`ShippingGen5EnvDeclClosed`、仮定として明示）

- Lean のカーネルは閉じた項だけを宣言として受理する、という不変量は `Environment` が core で不透明なので、Lean の中では導出できない。そこで `KernelClosedInvariant env`（`looseBVarRange = 0` の形）を **仮定の形の `Prop`** として置き、`envDeclClosed_of_kernel : OblLbrZero → KernelClosedInvariant env → EnvDeclClosed env` を証明した（名前付き `Prop` 間の含意。`OblLbrZero` は未解決のブリッジで、どこでも仮定していない）。
- 局所化: `EnvDeclClosedOn env R`、`envDeclClosedOn_univ_iff`（全体と同値）、`envDeclClosedOn_mono`、`envDeclClosedOn_of_list`、`envDeclClosed_of_on`（env の全保存名が `R` に入れば全体）。監査（有限の名前集合）が与えるのは `EnvDeclClosedOn` の形で、**全体の `EnvDeclClosed` は ALL 側の driver 環境ごとの検査**が与える。
- 仮定を満たす証拠は meta の検査（上）であって証明ではない。

### 3. ESProof の `CVEKL` への移植（`ShippingGen5ConstValueELProof`、axiom は propext / Classical.choice / Quot.sound のみ）

構文だけの補題（`liftS` / `substS` / `betaS` / `instForallS` の可換、`InsV`、`SafeArg`、`lbl_*`）は carrier を含まないのでそのまま再利用。carrier を含む補題を `CVEKS` → `CVEKL` に移した: `tdenl_wk` / `argsdenl_wk` / `cvekl_wk`、`SubVL` / `subvl_get` / `subvl_wk`、`tdenl_subst` / `argsdenl_subst` / `cvekl_subst`、`WfValL`、`oblDenBvarL`、`oblDenLitsL_of_rows`、`oblDenSubstL_safe`、`denTypedL`、`TyRKL` / `TyArgsL`、`KernelRulesKL`（`OblConstL` を新設）、`kernelRulesKL_TyRKL`、`tyRKL_sub`、`cvekl_tyRKS` / `cvekl_sound`。変更点は仮定 `EnvClosedS` → `EnvClosedL` だけで、証明は機械的に通った。さらに `cvekl_wk_of_declClosed` / `cvekl_subst_of_declClosed` / `denTypedL_of_declClosed` で、環境についての仮定が素の `EnvDeclClosed` だけになる形に言い直した。
未移植・未解決は変わらず: `OblDenSubstL` の一般形（Q1）、`RowArgsAtL` / `OblPrimArgsL`（Q2）。

### 4. 依存した codomain の 30 行（Q1/Q2 の承認後。今回は一覧と証明の形だけ）

`merge_row_typed_audit.py` を再実行した一覧（K1 の term key 115 件中、`Type 0`・引数あり・依存型。§Rows と同数）:
- 型・命題引数に依存: `Fin.mk`、`BitVec.ofFin`、`Decidable.isTrue`、`Decidable.isFalse`。
- `{dom : DomainConfig}` を取る出力 structure の `*.mk` 26 件: `Sparkle.IP.Bus.LINHW.ChkOut`、`Sparkle.IP.Crypto.Keccak256HW.KeccakFOut`、`Sparkle.IP.Crypto.Keccak256Sponge.SpongeOut`、`Sparkle.IP.Crypto.P256FieldHW.MulOut`、`Sparkle.IP.Crypto.P256OrderHW.MulOut`、`Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut`、`Sparkle.IP.Net.HFTStrategy.HFTOut`、`Sparkle.IP.Net.HTTP.HttpEmitOut`、`Sparkle.IP.Net.HTTP.HttpRequestParserOut`、`Sparkle.IP.Net.UART.TxOut`、`Sparkle.Tests.Compiler.MultiInstance.PeOut`、`Sparkle.Tests.Compiler.NoPortsMemKidTest.KOut`、`Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut`、`Sparkle.Tests.Compiler.ShippingMachineEntryTest.TwoOut`、`Sparkle.Tests.Compiler.ShippingMachineNestTest.Out` / `.Pair`、`Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut`、`Sparkle.Tests.Compiler.ShippingMachineTeleTest.CountOut` / `.PulseOut`、`Tests.Compiler.KaryGenTest.KOut`、`Tests.Compiler.KaryThreeTest.KOut`、`Tests.Compiler.SharedLeafGenDefaultHbTest.Acc16Out` / `.AccOutD`、`Tests.Compiler.SharedLeafGenFallbackTest.AccOutF`、`Tests.Compiler.SharedLeafGenTest.Acc16Out`、`Tests.Compiler.SharedLeafMemKidTest.MOut`（各 `.mk`）。

Q1/Q2 のあとの証明の形（**未証明の計画**）:
1. 宣言型 `T = Π (x₁:A₁)…(xₙ:Aₙ), D Ls (bvar 添字…)`（結果が `D` の spine で、引数が binder の bvar）について、`instForallS T args` を `n = args.length` で計算する補題: 各段の代入は本体の index 0 だけなので、`D Ls (args の対応する要素)` になる（binder の型 `Aᵢ` は `instForallS` が捨てる）。`ClosedPi` の一般化（`DepPi`）。
2. 結果の `TDenL` は `tcon` 規則で作る。型引数の `ArgsDenL` は `hargs` の対応位置から取り出す（`dom` は項引数なので `.tm`）。ここで行の仕様 `TmSpec`/`TyConSpec` を、引数の値に依存する形（`den as` の型が `as` の値の関数）に一般化する。
3. Q1 が要る箇所: `hargs` の導出と結果型の `TDenL` が同じ valuation・同じ引数式で閉じることと、`substS` が引数に lam / forall / const 頭を許すときの `TDenL` の代入（`OblDenSubstL` 一般形）。Q2 が要る箇所: 型引数・項引数が宣言型の binder 型に型付くこと（`RowArgsAtL`）。
観察（未証明、断定しない）: 1. の spine 計算自体は `SafeArg` を要求しないように見える。Q1 が実質必要になるのは 3 の代入の部分で、これは val 側の設計を見て確定する。

### 5. Check（`Tests/Gen5/SoundS3Check.lean`）と台帳

構造照合（移植した補題の型が `CVEKL` / `EnvClosedL` の形、`denTypedL_of_declClosed`、`kernelRulesKL_TyRKL` による束の充足可能性、局所化の同値）、負対照（空の表で junk entry の valuation は `WfValL` でない `junk_not_wf`、`Sort` は `TDenL` を持たない `sort_not_tden`、`lbr_bvar_not_closed`、`lam_not_safe`、空集合の `EnvDeclClosedOn` は自明、axiom 検出器）、37 宣言の axiom 検査（propext / Classical.choice / Quot.sound のみ）、`#print axioms` 5 件、残った義務 9 件が定理でも axiom でもなく `Prop` の定義であることの確認。

残った義務: `OblDenSubstL` 一般形（Q1）、`OblPrimArgsL` / `RowArgsAtL`（Q2）、`OblRowTypedS` の依存 30 行（Q1/Q2 後）、`KernelClosedInvariant`（カーネルの不変量、監査が証拠）、`OblLbrZero`（ブリッジ）。Lean の opaque な `instantiateLevelParams` との一致、kernel typing との一致は主張しない。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## §Final: 最終 carrier `CVFinal PT` と `FGLedgerPremisesStmtCV`（Issue `sparkle-ledger-dd4-final`、土台 fe106963 + par/sm1）

reviewer の方針: TRUSTED・axiom・sorry・native_decide なし。`PT` は明示的なパラメータのまま。G-PRIM の採用や TRUSTED 化は残余の一覧を見て別途判断するので、仮定に入れない。未解決のものは名前付きの前提（通常の仮説）にして条件付きで進める。**条件付きの成果は全体の健全性として主張しない。** net delta は決めない（census と対応の表だけ）。既存ファイルは書き換えていない。
土台: `FGLedgerPremisesStmtH`（SM1）が fe106963 に無かったので `par/sm1`（0fceecd7）を merge した（lakefile の append-only 衝突のみ、両方残した）。
新ファイル: `Tools/ShippingGen5CVFinal.lean`、`Tests/Gen5/CVFinalScan.lean`、`Tests/Gen5/CVFinalCheck.lean`。lakefile への lean_lib 登録は最初の commit で 1 回。

### 1. 最終 carrier と関数性（証明済み、axiom は propext / Classical.choice / Quot.sound のみ）

- `CVFinal PT : ConstValueRel := fun env X α v => CVLSKV PT env X α v`。すなわち `∃ τ, CVEKVL PT env [] (.const X (LS env X)) τ α v`（`CVEKVL` = `ShippingGen5ConstValueEVL.CVEKV`、固定 `LS env X`、valuation は `[]`）。
- `cvFinal_functional PT : ConstValueFunctional (CVFinal PT)`。**任意の `PT`、仮定なし**（排他性は env の kind で決まる）。`cvFinal_value_unique`（同じ型なら値も等しい）。
- `cvFinal_ne_top`: `CVFinal PT` は全関係 `fun _ _ _ _ => True` ではない（全関係は関数的でない `not_functional_top`）。
- `cvFinal_typed`: `EnvDeclClosed env` と `LitRows PT env`（`Nat` / `String` の 2 行）から、`CVFinal PT env X α v` の導出の型ラベルは `TDenV` で型付く（`denTypedVL_of_rows`、valuation `[]` は `wfValV_nil`）。`OblDenSubstS` は出ない。

### 2. `FGLedgerPremisesStmtCV`: H の CV binder を `PT` と名前付き前提に置き換えた文

- binder `CV : ConstValueRel` を `PT : PrimTableK` に替え、`CV := CVFinal PT`。第 1 conjunct は `ConstValueFunctional (CVFinal PT)`（**定理で、もう結論の仮定ではない**）。
- 名前付き前提（通常の仮説。axiom ではない）:
  - 外側（閉じた Prop）: `h_D_LBR : OblLbrZero`。
  - `EntryWitness` の直後（`envAt cref w` について）: `KernelClosedInvariant`（`EnvDeclClosed` は `envDeclClosed_of_premises` で `OblLbrZero` から出る）、`LitRows PT`、`OblRowTypedV PT`（`RowTypedAtV` の全 key。依存した 30 行を含む）、`∀ c ls, RowTeleEvAt PT`（引数の型付け。依存した 30 行を含む）。
- 橋: `fgLedgerPremisesStmtCV_of_H : H → CV 版`、`fgLedgerPremisesStmtCV_of_G : G → CV 版`（`CV := CVFinal PT` で特殊化し、余分な前提は捨てる）。
- **CVTopCheck の反駁は CV 版では成り立たない**: 反駁は `CV` が自由な全称 binder で `CV := ⊤` を代入できることに依る。CV 版には `ConstValueRel` の binder がない（Check で H 1 → CV 0）。第 1 conjunct は `cvFinal_functional`、`CVFinal PT ≠ cvTop`（`cv_not_top`）。ただし**これは文が真であることを示さない**（下の 5）。

### 3. `DeclConnect (CVFinal PT)` の意味

- `declConnect_cvFinal_iff`（定義の展開）: 各 target `X` と package `p` について、`env.find? X = some ci`、`shapeOf ci = some sh`、`ShapeMatches sh p.d p.kD`、**`∃ τ, CVEKVL PT env [] (.const X (LS env X)) τ sh.Ty v`**、`sh.obs v = p.src` を満たす `v`。
- 証明できた部分: 値の一意性（`declConnect_cvFinal_unique`、関数性から）、`EnvDeclClosed` と `LitRows` の下での型ラベルの型付け（`declConnect_cvFinal_typed`）、`declConnect_mono` は DeclConnect.lean のまま使える。
- 残り（名前付き前提 / 未証明）: **存在**（`∃ v, CVFinal PT env X sh.Ty v`: `prim` の `hty` / `hargs` を作る行 = `RowTypedAtV` / `RowTeleEvAt` と `PT` の中身、`unfold` の本体の導出）、`obs v = p.src`（`DeclConnect` の rows = D.D-5）。

### 4. 入った前提と台帳の行 ID の対応（`CVFinalCheck` が `scripts/gen2/PREMISE_LEDGER.md` を読んで確認）

| 前提 | 型 | 台帳の既存行 | 判定 |
|---|---|---|---|
| `PT`（binder） | `PrimTableK` | D.D-4（carrier `CV`）の置き換え。D.D-4 の「ConstValue の定義が未記述」は `CVFinal` で書けた。**`PT` の中身の行は台帳にない** | 既存行を置き換える。PT の行は新規（G-PRIM の判断待ち） |
| `h_D_LBR` | `OblLbrZero` | なし（台帳に 0 件） | **新しい行** |
| `KernelClosedInvariant` / `EnvDeclClosed` | env の事実 | なし（0 件） | **新しい行** |
| `LitRows PT` | `PT` の条件 | なし（0 件） | **新しい行**（`PT` の仕様） |
| `OblRowTypedV PT`（`RowTypedAtV`） | 行ごとの `hty` | なし（0 件） | **新しい行** |
| `∀ c ls, RowTeleEvAt PT` | 行ごとの引数の型付け | なし（0 件） | **新しい行** |
| `DeclConnect` の存在・`obs` | 結論 | D.D-5（DeclConnect の rows）のまま | 既存行 |

対応は census と台帳の文字列照合の結果であって、行の数え直しではない。**台帳の数（FG 75 / T1 57）は変えていない**。新しい行を台帳に足すか、既存の D.D-4 / D.D-5 に合算するかは reviewer の判断（net delta は決めない）。

### 5. census と Check（`Tests/Gen5/CVFinalCheck.lean`、`CVFinalScan.lean`）

- H と CV 版の構造比較: removed `[CV]`、added `[PT, h_D_LBR]`、changed `[]`、第 1 conjunct `==`、内側の仮説は removed 0・added 4（`KernelClosedInvariant`、`LitRows`、`OblRowTypedV`、`RowTeleEvAt`）、結論は `CV := CVFinal PT` の代入後 `==`。`ConstValueRel` の binder は H 1 → CV 0。外側 binder 13 → 14、内側の仮説 11 → 15。G と比べると removed は `[initsOf, hs, CV]`。
- 負対照: 代入しない比較は失敗、`CV := cvTop` は失敗、H と H は空、CV と H（逆向き）は失敗、axiom 検出器は利用者 axiom とそれを使う定理を検出。`not_litRows_nil`（空の表は `LitRows` を満たさない）、`litRows_lit`（`Nat` / `String` だけの表は満たす）、`rows_nil`（**行の前提は空の表も満たす**: `OblRowTypedV PTnil`・`RowTeleEvAt PTnil`）。
- Scan（`CVFinalScan`）: 旧 carrier の帰納型 16 個（`CVE` / `CVEKS` / `CVEKL` / `CVEK` と EV の opaque 版、およびその `TDen*` / `ArgsDen*`）。最終 root 13 件の閉包（到達 5897 定数）と consumer 7 件（`DeclConnect`、`ConstValueFunctional`、H、G、`genGP` ほか。到達 5552）は旧 carrier に**到達しない**（hits 0）。旧 root 5 件（`cvlsks_functional`、`cvls_functional`、`cvlskl_functional`、EV の `cvlskv_functional`、`CVLSK`）は検出される。旧理論は履歴と比較のために残してある。

### 6. 主張しないこと / 残り

- **条件付きの成果であり、全体の健全性は主張しない。** 名前付き前提 5 つは解いていない（`OblLbrZero`、`KernelClosedInvariant`、`LitRows`、`OblRowTypedV` の依存 30 行ほか、`RowTeleEvAt` の依存 30 行）。
- **`PT` を全称のまま残した文の限界（観察。証明はしていない）**: 行の前提は空の表 `PTnil` も満たす（`rows_nil`）。`LitRows` だけが空の表を除く。`DeclConnect (CVFinal PT)` の存在は `PT` の中身に依るので、`∀ PT` の文が真であるには前提が足りない可能性が高い。これが G-PRIM（`PT` の固定または TRUSTED 化）の判断材料。今回は仮定に入れていない。
- 旧 `CVEKS` の導出からの写像、kernel typing との一致、`Expr.instantiateLevelParams` と `instantiateLevelParamsS` の一致、実際の `PT` が仕様を満たすこと。

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。


## §Final2: `PTlit` による ∀ PT の反駁と、具体的な `PTcorpus`（Issue `sparkle-ledger-dd4-final`、土台 18af4bc3）

reviewer の方針: PT を全称のままにせず具体的な PTcorpus へ進む。PTnil は LitRows を満たさないので反例ではない。PTcorpus の採用・新 TRUSTED・台帳の減算・最終保証は承認されていない。5 つの名前付き前提のまま条件付きで続ける。TRUSTED・axiom・sorry・native_decide なし（axiom は propext / Classical.choice / Quot.sound のみ）。既存ファイルは書き換えていない。
新ファイル: `Tools/ShippingGen5PTLit.lean`、`Tests/Gen5/PTLitCheck.lean`、`Tools/ShippingGen5PTCorpus.lean`、`Tests/Gen5/PTCorpusCheck.lean`、`scripts/gen5/GenPTCorpus.lean`（生成器。出力を読んで commit し、kernel が検査する）、`scripts/gen5/ptcorpus_{keys,missing,closure}.tsv`。

### 1. 反駁: `PTlit`（Nat / String の literal 行だけ）では Signal の root が導出できない

- `PTnil`: `LitRows PTnil env` は偽（`ptnil_not_litRows`）。ゆえに `PTnil` は最終文の反例ではない（§Final 6 の記述を修正する: `rows_nil` が示すのは行の前提 2 つが `PTnil` で満たされることだけ）。
- `PTlit`（`natRow` / `strRow`、`tms` は全部 `none`）: `LitRows PTlit env` は env の事実 `¬IsDefn env Nat` / `String` から（`ptlit_litRows`）、`OblRowTypedV PTlit env` と `∀ c ls, RowTeleEvAt PTlit env c ls` は `tms` に行がないので無条件（`ptlit_oblRowTypedV`、`ptlit_rowTeleEvAt`）。残る 2 つの前提 `OblLbrZero`・`KernelClosedInvariant` は `PT` に依らないので、そのまま仮定として残る。**補助の前提 4 つ（のうち PT に依るもの）は PTlit で満たされる。**
- 導出に `prim` は使えない（`tms = none`）。`StuckB env e`（head が定義でない定数 / 定義の展開が stuck / 束縛型の head が Nat・String 以外で定義でない `lam` / body が stuck の `lam`）なら、どの valuation でも `CVEKVB PTlit env ρ e …` はない（`stuckB_no_cvekvb`、`cvekvb_const_head`、`tdenv_const_head`）。
- 帰結（kernel 検査済み）: `StuckB env (const X (LS env X))` かつ `P X = some p` なら `¬ DeclConnect (CVFinal PTlit) env P Tgt`（`ptlit_not_declConnect`）。`stmtCV_ptlit_refutes_entry`: `FGLedgerPremisesStmtCV` ＋ entry run の仮定 ＋ 上の補助前提 ＋ `StuckB`（`declName` 自身。`TgtRun.top`）から `False`。
- 具体の root（`Tests/Gen5/PTLitCheck.lean`、meta。**env の事実の評価であって、その env についての kernel の証明ではない**。含意は kernel の `stuckChk_sound`）: `Sparkle.Tests.SignalLoopTest.counterLoop`（`Signal.loop` に展開され、head が `Signal.mk`＝定義でない）、`shift4Loop` と `counterEnableLoop`（`lam` の束縛型の head が `Signal`）。3 つとも `stuckChk … = true`。`Nat` / `String` は定義でないことも評価。負対照: literal・`bvar`・`fun (x : Nat) => x` は stuck でない。`PTlit` が空でない確認: `natLit` / `strLit` の導出がある。
- **結論**: `∀ PT` の文は `PTlit` で偽（entry run の仮定が充足可能なら）か空虚（充足不能なら）。どちらかは示していない（`EntryWitness` などの充足可能性は未確認）。ゆえに PT を任意のまま最終形にできない。

### 2. `PTcorpus`（`Tools/ShippingGen5PTCorpus.lean`）

- 行は Lean の項: `TmTele ks` / `TyTele ks`（kinds を添字にした値の telescope: `tm A (fun a => …)`、`ty (fun T => …)`、`done R v`）。コンストラクタ行はコンストラクタそのもの（`Nat.succ` は `tm Nat (fun n => done Nat (Nat.succ n))`）。`run` は項引数を型 `A` のときだけ受ける（cast は `Classical.propDecidable`）。表は `tysTable` / `tmsTable`（key = 名前 × 数値の level）、`PTcorpus : PrimTableK` は表の検索。生成器が K1 の 204 key（ctor 100 / rec 15 / induct 89。`PrimResidueKey*` の再実行で復元、`scripts/gen5/ptcorpus_keys.tsv`）の宣言型から行を作る。
- 行ができた key: **型 50 + 項 51**（K1 の 98 ＋ 閉包 3: `String`（literal の規則が使う）、`ActiveEdge`、`ResetKind`（行の宣言型に現れる）。K1 の残余の表は型の行の閉包になっていなかった）。
- 行がない key: **106**（理由別、各 key は `missingTable`）: 再帰子 15（motive が `Sort` への関数で `Arg` / `Dyn.ty : Type` に入らない）、corpus の宣言 51（output 構造体と test の型。`Tools` から 47 module を import できない、うち 4 つは同時に import できない）、`Type 0` に入らない束縛 25（`f : Type → Type` の型クラス `Functor` / `Monad`、`PProd.{1,_}` ほか）、証明の束縛 6（`Fin.mk`、`Decidable.isTrue/isFalse`、`Nat.le.step`、`HEq`、`HEq.refl`）、結果が Prop か `Type 0` の外 4、族が Prop か `Type 0` の外 5。
- 行ごとの証明（env の事実は仮定のまま。`PTCorpusCheck` が実環境で評価）: `TmSpec` / `TyConSpec` は構成から（`TmTele.spec`）。**`RowTypedAtV` を 32 / 51 行**: 引数なし 6、閉じた codomain 3（`Nat.succ`、`Int.ofNat`、`Int.negSucc`）、`DomainConfig.mk`、第 1 引数に依存する 22（`Add.mk` などの型クラス構造体、`List.nil/cons`、`Array.mk`、`Wireable.mk`。`firstArgSpec_ty` + `rowTypedAtV_depFirst`）。**`RowTeleEvAt` を 10 / 51 行**（引数なし 6 ＋ 定数の telescope 4）。`LitRows PTcorpus` は 2 つの env 事実だけから（`ptcorpus_litRows`）。
- 開いた義務（行ごとの名前付き。`PTCorpusCheck` が一覧を出す）: `RowTypedAtV` 19 行（`H*.mk` 12、`Pow.mk`、`OfNat.mk`、`Prod.mk`、`PProd.mk`、`HasDomain.mk`、`Signal.mk`、`BitVec.ofFin`＝引数に依存する結果が第 2 引数以降か Prop の束縛）、`RowTeleEvAt` 41 行、行がない key 106。
- DeclConnect の存在の脚: `Tests.SignalLoopTest` の 3 つの Signal root が到達する残余 key のうち行がないのは **29 / 75、20 / 59、29 / 75**（再帰子 `Bool.rec` / `Nat.rec` / `Decidable.rec` / `Eq.rec` / `False.rec` / `Nat.le.rec`、Prop の束縛、`Functor` 系）。到達集合は `PrimResidueKey` の近似（導出が必ず通るとは限らないが、本体の構成要素はすべて評価される）。**したがって `PTcorpus` でも、再帰子を使う root（K1 の roots の大半）の `DeclConnect` の存在は払えない**。再帰子の行は `Dyn`（`Type 0`）に入らず、行の追加では解決しない。TRUSTED か carrier の拡張（motive を持てる値の型）が要る。これは reviewer の判断であり、ここでは採用していない。

### 3. `PT := PTcorpus` の文と census（`Tests/Gen5/PTCorpusCheck.lean`）

- `FGLedgerPremisesStmtPTC`（`FGLedgerPremisesStmtCV` から binder `PT` を除き `PTcorpus` を固定）。`fgLedgerPremisesStmtPTC_of_CV`、`_of_H`（kernel 検査済み）。
- census: CV → PTC は removed `[PT]`、added `[]`、内側の仮説 15 → 15（変更なし）、外側 binder 14 → 13、`PrimTableK` の binder は 0。H → PTC は removed `[CV]`、added `[h_D_LBR]`、内側 +4（`KernelClosedInvariant`、`LitRows`、`OblRowTypedV`、`RowTeleEvAt`）、外側 13 → 13。負対照: `PT := PTcorpus` の置換なしでは census が通らない。
- 残った義務の数と種類: 名前付き前提 5（`OblLbrZero`、`KernelClosedInvariant`、`LitRows PTcorpus`＝2 つの env 事実に還元できる、`OblRowTypedV PTcorpus`＝上の 19 行が開いている、`RowTeleEvAt PTcorpus`＝41 行が開いている）＋ 行がない key 106（うち再帰子 15）。**net delta は決めない。**

### 4. 主張しないこと

- `PTcorpus` の採用、G-PRIM、TRUSTED、台帳の減算、最終保証。K1 の 204 key 以外の残余（`PRIM_RESIDUE_FULL.md` の 379 定数のうち 175 は未着手）。
- `PTlit` の反駁が実際の `EntryWitness` などの充足可能性を含むこと。導出がないことの meta 評価は env の事実の監査であり、kernel の証明はその含意の側だけ。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## §Shard: 共有 PT core + 宣言・module ごとの extension shard（Issue `sparkle-ledger-dd4-shard`、土台 bc4e180f）

reviewer の判断 Q-B: corpus の宣言（output 構造体など）を Tools の共通表に押し込まず、共有の core（`PTcorpus`＝`PTcore`）に、宣言または module 単位で生成する shard を足し、各 root は要る shard だけを合成する。**PTcorpus の採用・G-PRIM・TRUSTED・D.D-4 の減算・最終保証は未承認のまま。** TRUSTED・axiom・sorry・native_decide なし（axiom は propext / Classical.choice / Quot.sound のみ）。既存ファイルは書き換えていない。
新ファイル: `Tools/ShippingGen5PTShard.lean`、`Tests/Gen5/PTShard/*.lean`（生成された shard 23 本）、`Tests/Gen5/PTShardCheck.lean`。lakefile は lean_lib 3 つ（`Tools.ShippingGen5PTShard`、`Tests.Gen5.PTShardCheck`、`Tests.Gen5.PTShard`＝submodules）。

### 1. shard の型と合成（`Tools/ShippingGen5PTShard.lean`、kernel 検査済み）

- `PTShard`: `tys` / `tms` の表（`PTcorpus` の `tysTable` / `tmsTable` と同じ形: key = 名前 × 数値の level、行 = `TyTele ks` / `TmTele ks`）。`PTShard.toPT : PrimTableK` は `PTcorpus` と同じ検索。core は表 2 つからなる shard（`ptcore_eq : PTcore = PTcoreShard.toPT` は `rfl`）。
- 合成 `A ⊕ₚ B`（`comp`）は左優先の和。**排他** `Excl A B` は「どの key でも片方は行がない」。`comp_tys_left`/`comp_tms_left`（左の行は常に残る）、`comp_*_right_excl`（`Excl` なら右の行も残る）、`comp_comm`（`Excl` なら順序によらない）、`comp_assoc`、`Excl.comp_left`（合成を左に持つ排他）。
- `FreshAgainst PT S`: shard `S` の key（数値 level）すべてで `PT` に行がない、という `Bool` の文。`FreshAgainst.excl : FreshAgainst PT S → Excl PT S.toPT`（shard の行は自分の key にしかない、が `toPT_*_some`）。生成物ごとに `rfl` で払う。
- **`cvFinal_comp_functional : ConstValueFunctional (CVFinal (A ⊕ₚ B))`**。これは任意の `PrimTableK` で成り立つ `cvFinal_functional` の特殊化で、`Excl` を使わない（関数性は合成に対して無条件に保たれる。`Excl` が保証するのは、両側の行が欠けも変わりもしないこと）。
- 補足: 合成したのは表であって、`FGLedgerPremisesStmtPTC` の `PT := PTcorpus` を root ごとの `PT := PTcore ⊕ shards` にした文は**まだ作っていない**（`FGLedgerPremisesStmtCV` は `PT` を束縛するので `PT := PTcore ⊕ₚ …` への特殊化は同じ手で作れる。今回はしていない）。

### 2. 生成の仕組み（`#pt_shard`、`#pt_shard_module`）

- `#pt_shard S₁ S₂ …`（宣言ごと）と `#pt_shard_module M`（module ごと: `M` が宣言する帰納型を名前順に、internal / private を除いて）。型 former と各 constructor について、**環境にある宣言型**から行を作る（`A : Type` の束縛は型引数、`A : Type` の項は項引数。証明の束縛・`Type 0` 外の束縛・結果が `Type 0` 外は行なし＝`ptShardMissing` に理由つきで残す）。生成したソースを parse して elaborate する通常の宣言なので、型検査は kernel が行う。
- 生成物（shard ごとの namespace）: `ptShardTy<i>` / `ptShardTm<j>`（行の項。`@S.mk x₁ … xₙ` は実際の constructor として型検査される）、`ptShard : PTShard`、`ptShardWanted` / `ptShardMissing`（要求した key / 行がない key と理由）。
- **key ごとの theorem**: `…_key`（`ptShard.toPT` の検索が行そのもの、`rfl`）、`…_run`（行を宣言型の束縛の型の引数で走らせると、constructor の適用と宣言どおりの結果型が返る。型 former は `some (@S x₁…)`、constructor は `some ⟨R, @S.mk x₁…⟩`。`simp` で kernel が検査）、`…_comp`（`PTcore ⊕ₚ ptShard.toPT` でも同じ行が見つかる）。
- shard ごとの theorem: `ptShard_fresh`（core に対する `FreshAgainst`、`⟨rfl, rfl⟩`）、`ptShard_excl`、`ptShard_nodup`（shard 内の key 重複なし、`decide`）、`ptShard_n_tys` / `n_tms` / `n_wanted` / `n_missing`（件数、`rfl`）、`ptShard_functional`。

### 3. 生成した shard と Check（`Tests/Gen5/PTShardCheck.lean`、build exit 0）

- 生成した shard: 23 本（`Tests.SignalLoopTest`、corpus の宣言 51 key を持つ 22 module。`Tests/Gen5/PTShard/*.lean` は各 5 行ほど: import と `#pt_shard_module M` だけ）。23 本とも 1 つの Check に同時に import できた（個別 build も exit 0）。
- **`Tests.SignalLoopTest` の shard は空**（0 型・0 項）。この module は帰納型を宣言しないので、3 つの Signal root（`counterLoop`、`counterEnableLoop`、`shift4Loop`）が必要とする行は core にあるか、**core にも shard にも置けない key**（再帰子・Prop の束縛・`Functor` 系）のどちらかで、shard では何も増えない。§Final2 の 29/75・20/59・29/75 は shard で変わらない。
- 件数（kernel の `decide` / `rfl`）: 型 30 + 項 30 = 60 key（shard の行がない key は 0）。**`PTcorpus` の `notImportable` 51 key のうち 51 件を shard で払えた**（`n_paid`、axiom なし）。`unpaid = []`。余分の 9 key（`Pair`、`PidOut`、`Lanes25`、`HttpStatusParserOut`、`RxOut` とそれらの `mk`）は K1 のリストにはなく、module の宣言として生成されたもの（payment には数えない）。key は shard 間で重複せず（`paid_nodup`）、core の key とも重ならない（`paid_not_in_core`）。
- root の合成の例: `rootPT := PTcore ⊕ₚ KaryGen ⊕ₚ MachineTele ⊕ₚ MachineNest ⊕ₚ SignalLoop`。各段の shard が直前までの合成に対して `FreshAgainst`（`fresh_step1`〜`4`、`rfl`）、core の行が残る（`rootPT_keeps_core_tys`）、`MachineNest` の行が残る（`rootPT_keeps_nest_ty0`）、`rootPT_functional`。負対照: core 自身を shard とみなすと `FreshAgainst` は偽（`not_fresh_core_shard`）。
- env の監査（meta。**kernel の証明ではない**）: 60 key すべてで定数が環境にあり、行の kinds の数が宣言型の束縛の数と一致（不一致 0）。

### 4. 主張しないこと / 残り

- shard の行は `TmSpec` / 結果型の事実（`…_run`）までで、**`RowTypedAtV` / `RowTeleEvAt` は shard の行について出していない**。output 構造体の constructor は結果型が第 1 引数（`dom : DomainConfig`）に依存する（`KOut dom`）項の依存で、`PTcorpus` で開いている `Signal.mk` と同じ型の義務。51 key を「払えた」は**行を置けた**であって、行の健全性（`OblRowTypedV` / `RowTeleEvAt` の 2 つの名前付き前提）は変わらない。台帳は動かさない。
- §Final2 の「4 つは同時に import できない」の 4 つがどれかは特定していない。この 23 本は 1 つの Check に同時に import できたので、少なくともこの組合せには衝突がない。衝突する組があれば、各 root は両方を import できないので、その root は片方の shard だけを合成する（shard が module 単位に分かれている理由）。
- 再帰子 15 / `Type 0` 外 25 / 証明の束縛 6 / 結果が Prop か `Type 0` 外 4 / 族が Prop か `Type 0` 外 5 は shard では払えない（行の形が `Dyn` に入らない）。Q-A の領分。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。
