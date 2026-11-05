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
