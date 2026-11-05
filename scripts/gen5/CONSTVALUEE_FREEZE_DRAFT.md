# `ConstValueE PT` — freeze 草案（D.D-4、案 B）。草案であり、採用ではない

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
