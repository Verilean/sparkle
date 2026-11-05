# D.D-4: 最終 FG の carrier `CV` を固定する — ユーザー判断のための資料

Issue `sparkle-ledger-dd4`（台帳行 D.D-4。関連する Issue `sparkle-gen5-dc-connect`）。土台: par/cvtop 40b176fe（土台 f9dbc699）。文書のみで、Lean と build の変更はない。
この資料は前提知識なしで読めるように書いた。各判断項目はそれだけで読めるようにしてある。選択肢 A〜D の定義は
`scripts/gen5/DC_CONNECT_PRIM_TABLE_DECISION.md` rev5（以下「rev5」）のとおりで、ここでは変えていない。

## 1. 背景（やさしい言葉で）

### 1.1 FG とは
FG は gen5 系の最終定理である。「コンパイラが成功した各宣言について、(1) 生成したハードウェアはパッケージ `p.src` と同じ動きをする、
かつ (2) `p.src` は、その宣言が Lean の中で意味するものと同じである」と述べる。(1) はこれまでの証明の積み重ねで、(2) が本資料の話題である。

### 1.2 `CV` とは
`CV`（型 `ConstValueRel := Environment → Name → (α : Type) → α → Prop`、`Tools/ShippingGen5DeclConnect.lean:267`）は、
「環境 `env` の中で名前 `X` の宣言は、型 `α` のこの Lean の値 `v` を意味する」という関係である。
つまり「宣言の Lean での意味」を、コンパイラが扱うデータ（`Environment`、`ConstantInfo`、`Expr`）の上で定義したもの。

### 1.3 `DeclConnect` が求めること
`DeclConnect`（`:274`、展開式は `declConnect_eq` `:281`）は、到達する各名前 `X` とそのパッケージ `p` について、
宣言 `ci` と信号の形 `sh` と値 `v` があって、`CV env X sh.Ty v ∧ (v の観測) = p.src` であることを求める。
「宣言の意味 `v` が存在し、それを観測するとパッケージと一致する」という要求である。

### 1.4 `ConstValueFunctional` とは
`ConstValueFunctional CV`（`Tools/ShippingGen5FG.lean:22`）は「一つの名前に意味は一つしかない」（二つの値があれば型も値も等しい）という性質。
これを使う証明は `dcImp_of_dcGen`（`Tools/ShippingGen5DeclConnectAbs.lean:64`）だけである（`git grep` で確認。他は Check の文面比較のみ）。

## 2. 見つかった欠陥（reviewer が認定）

今の最終の文 `FGLedgerPremisesStmtG`（`Tools/ShippingGenFGLedgerPremisesG.lean:74,82`）は、`CV` を**何の前提もなしに全称で**束縛しながら、
結論の第 1 項に `ConstValueFunctional CV` を置いている。その結果:

| 事実 | Lean の根拠 | 意味 |
|---|---|---|
| `CV := cvTop`（何でも真）では関数性が偽 | `cvTop_not_functional`（`Tests/Gen5/CVTopCheck.lean`、40b176fe） | `Unit` と `Bool` の値を同じ名前に結べてしまう |
| G から外側の 3 仮説の矛盾が出る | `fgG_refutes_outer`（同） | 文 G は偽か空虚（R も `fgLedgerPremisesStmtG_of_R` 経由で同じ） |
| `CV :=` 空の関係では DeclConnect が偽 | `not_declConnect_of_empty`（`ShippingGen5DeclConnect.lean:291`） | 存在の要求が満たせない |

実行: `kjob-run-src-cvtop-8246` exit 0、axioms は標準（propext, Classical.choice, Quot.sound）のみ、sorry なし。

このため、次の 2 つの直し方は**採らない**（台帳 §12.22、par/fg-ledger-sync bac6a3ac）:
- (b) `ConstValueFunctional CV` を前提へ移す: `cvTop` のような関係も許すことになり、最終の文が「関数的な何かについて」の弱い主張に変わる。さらに空の関係で前提を満たせば DeclConnect は偽で、意味のある保証にならない。
- (c) `∃ CV` とする: 都合のよい関係を後から選べるので、「宣言の意味」という主張が空になる。

結論: **最終の組立の前に、`CV` を一つの固定した定義 `ConstValueE PT` にする必要がある**（DC_CONNECT_FREEZE rev5 §C.6、l.388-391）。
これは方針であり、ここでは判断を求めない。判断を求めるのは、その定義の中の「基本操作の表 PT」をどう扱うか（§4）である。

## 3. `ConstValueE PT` とは何か

`Expr` の小さな解釈器を、**帰納的に定義された最小の関係**として書く（再帰関数ではないので停止性の主張は要らない）。規則は 2 種類ある（freeze §C.6 の表）。

| 規則 | 内容 | 信頼が要るか |
|---|---|---|
| lit | 数・文字列リテラル ↦ その値 | 不要（D: 構造から定義） |
| bvar | 変数 ↦ 環境の値 | 不要 |
| lam | `fun x => b` ↦ Lean の関数 | 不要 |
| app | `f a` ↦ 関数適用（型の対応 `TypeDenotes` を確認） | 不要 |
| let | `let x := v; b` ↦ `x := ⟦v⟧` で `b` | 不要 |
| const-unfold | `env.find? c = some (.defnInfo d)` ↦ `d` の本体の意味 | 不要 |
| const-prim（表 PT） | 展開できない、または展開しない定数: `Signal.register`、`Signal.loop`、`BitVec.*`、`Bool.*`、`Prod.mk/fst/snd`、`ite`、`Nat.add`、コンストラクタ、再帰子など ↦ 名前を付けた Lean の項 | **要る（T）** |
| 型の基本形 | `Signal`、`BitVec`、`Prod`、`Bool`、`Nat`、`DomainConfig`、`Pi ↦ →` | **要る（T）** |

表 PT の各行は「`Name` というデータ `Prod.mk` は、Lean の定数 `Prod.mk` のことだ」という対応である。Lean のカーネルは自分自身の定数とデータの
対応を検査できないので、行が正しいことは証明できず、TRUSTED に近い性質を持つ（行が正しいかを信じることになる）。表自体は普通の `def` で、axiom は入らない。

関数性 `ConstValueFunctional (ConstValueE PT)` は証明する予定だが、まだ書いていない（freeze §C.6 (a)-(d)）:
- (a) 全規則の帰納的な一覧（前提と型付けを含む）を、この単位の freeze として固める。
- (b) const-unfold と const-prim の排他性または整合性。例: unfold 側に `c ∉ PT.dom` を付ける（規則が重ならない）、または名前ごとに「表の項 = 展開した本体の意味」を示す。
  表が名前ごとに 1 行であるだけでは足りない（rev5 の R2 訂正: 同じ名前が unfold と prim の 2 通りで導出されうる）。
- (c) lit/bvar/lam/app/let と `TypeDenotes` の決定性。
- (d) 2 つの導出についての帰納法による関数性の証明。

規模の見込み（**測っていない推定**）: 複数の単位、合計 1〜2 千行程度、独自の freeze を 1 本持つ。表の行数は未測定（rev5 §5）。

## 4. 判断項目: 表 PT の扱い（選択肢）

rev5 §3 の定義をそのまま引用し、表を持たない案を加える。どの案でも**データの損失はない**（変わるのは証明の成果物と文書だけで、コンパイラ出力・既存ファイル・既存の証明は変わらない。C/D は別記）。

| 案 | rev5 の定義（引用） |
|---|---|
| A | "If derivation of the rows turns out to be impossible for some of them: adopt the stated rows as a TRUSTED boundary (G-PRIM; the rows are listed in the report, FG's final statement is "uniform" and relative to it). Not shown to be needed" |
| B | "A *minimal* table: unfold every `defnInfo` (const-unfold) and leave in the table only the constants with nothing to unfold (constructors, recursors, quotient primitives, opaque/`extern`/`implemented_by`, type formers)" |
| C | "Do not adopt a table: keep G3-DECL per declaration (state (i) of `GENERAL_SPEC.md:501-503`, a CONDITIONAL result reported row by row)" |
| D | "Have the compiler emit a kernel-checked per-declaration link and take a uniform statement from it" |
| 表なし | （本資料で追加）PT を空にし、D 規則だけで `ConstValueE` を作る |

### 4.1 各案の影響

| 案 | 利用者に見える保証の変化 | Signal 基本操作の存在行（`∃ v, CV env X sh.Ty v`） | 新しい TRUSTED | コスト | 運用リスク | 戻せるか |
|---|---|---|---|---|---|---|
| A | FG は「一様」だが、名前付きの信頼リスト G-PRIM に相対的になる（G7 の隣に 1 項目増える） | 表の行で導出できる | **あり**（表の行） | 表の作成（大きさ未測定）、`ConstValueE` の freeze、関数性の証明。各行のビルド時メタ検査（名前が解決し、型が行の型と一致）は監査であって証明ではない | 行の誤りがあると、その行に依存する宣言の保証が誤る。行数が多いとレビューが重い | はい（表は追加の `def`。外せば今の状態に戻る） |
| B | A と同じ種類の境界だが、より小さく一様（カーネルの基本要素の行だけ） | `defnInfo` は展開、残りは表で導出 | 残余の行だけ（残余が空なら**なし**） | 宣言ごとの展開が増える。再帰子の行に `RecursorVal.rules` からの一般規則が要り、`Expr` 簡約の形式化が大きくなる可能性 | 残余の大きさが未測定で、レビュー可能な大きさかは調査次第 | はい |
| C | **保証の変更**: FG は宣言ごとの G3-DECL を条件とする「条件付きの結果」として行ごとに報告（GENERAL_SPEC:503-504 でユーザー判断が要る） | 一様には払わない（宣言ごとに `X.machine_source` の `rfl` で確認する今のまま） | なし | 今はなし。ただし今の文は反駁されるので、DeclConnect を一様な結論から外す書き換えは要る | M5 の完了条件（一様な前提だけで FG）を満たさない | はい（後で A/B に進める） |
| D | 保証の文面は同じで、証拠が強くなる | コンパイラが宣言ごとにカーネル検査済みの対応を出す | なし | コンパイラ（`Elab*.lean`）の変更。ユーザー承認なしでは禁止。規模不明、設計なし | コンパイラ出力が変わる（出力方針: 機能確認・面積/速度の計測・記録が要る） | 変更を戻せばよいが、コンパイラ変更なので手間は大きい |
| 表なし | 文は一つの定義に固定され、反駁はなくなる（関数性は証明できる見込み） | **払えない**。`Signal.register` などや型の基本形 `Signal`/`BitVec` に規則がないので、それらを含む宣言では存在行が導出できない | なし | `ConstValueE` と関数性の証明だけ（表の分は不要） | FG の文は書けて矛盾しないが、実際の宣言について存在行が証明できず（その宣言では DeclConnect が成り立たない可能性もある）、FG は完成しない | はい |

## 5. プロジェクトの目標への影響

- 現在値: **FG 77 / T1 57**（台帳 §12.21、§12.22 で数は変えていない。par/fg-ledger-sync bac6a3ac）。
- 止まっているもの: `sparkle-gen5-decl-bridge` の最終組立（`FG-REF ∧ ConstValueOk ∧ DeclConnect`）と M5 の G3-DECL の解消。CV が固定されるまで組立は完了できない。
- 止まらないもの: U-UNIV、U-SHAPE1/2、U-ROWS、U-ENTRY、`ConstValueE` の規則設計と最小表の調査（rev5 §5）、他の台帳行の作業。

D.D-4 の行の見込み（**見込みであり、減算はレビュー後に台帳の規則で数える**。行は最終定理の binder が変わったときだけ消える）:

| 案 | D.D-4 の行 |
|---|---|
| B（残余なし） | 消える（CV が定義になり、関数性が定理になる。存在行は D.D-5 の rows 側で払う） |
| B（残余あり）/ A | 消えて、TRUSTED の行 G-PRIM（列挙した表の行）に置き換わる |
| C | 残る（宣言ごとの条件として、形を変えて残る） |
| D | 原理的には消える。ただしコンパイラ変更の承認と設計が先 |
| 表なし | 反駁は消えるが、存在行が払えない前提として残る（実質的に残る） |

## 6. 推奨

**B を先に進め、表に残る行（残余）があればその分だけを A の TRUSTED 境界（G-PRIM）として明示して採る**（rev5 §4 と同じ）。理由:
- FG の強さ（一様な保証）を保つ。C は保証を弱める変更で、A/B が無理と分かるまでは勧めない。
- axiom を入れない。表は普通の `def` で、残余の各行にはビルド時のメタ検査を監査として付け、TRUSTED と明記して報告する。
- 信頼する範囲が展開で可能な限り小さくなる。`defnInfo` を展開すれば、`Signal.register` のような定義を表に置かずに済み、§3 (b) の排他性も「unfold できるものは表に置かない」で単純になる。
- 表なしは TRUSTED が要らないが、Signal 基本操作の存在行が払えず FG が完成しない。D はコンパイラ変更の承認と設計がなく、今は選べない。

なぜ A より B を先にするか: rev5 は「新しい TRUSTED が必要」とはまだ示されていないとしている（R2 訂正）。どの行が導出でき、どの行が述べるしかないかは、
最小表の調査（最大展開後に残る異なる定数の数をコーパスで数える）と規則一覧ができるまで分からない。B の調査をしてから、残余だけを A として扱う。
推奨は、その残余がレビュー可能な大きさであることを条件とする（未測定）。

ユーザーに今お願いしたいこと: (1) B を先に進める方針の了承、(2) 調査の後、空でない残余を TRUSTED（G-PRIM）として採ってよいか。(2) は残余の一覧ができた時点で、行の一覧を付けて改めて確認する。
新しい TRUSTED はユーザーの承認前には入れない（D_M5t2 D-4: `seq3553`「新 TRUSTED 採用は未承認」）。

### 判断しない場合
- G/R の文は中間の結果のまま（`FG_CONNECT` は `CV` を引数に取る形）で、そう報告する。完了とは言わない。
- 最終組立は完了できない。D.D-4 は残る。
- B の調査（規則一覧・最小表の数え上げ）と他の台帳行の作業は続けられる。TRUSTED を入れるかどうかの点に来たところで止まる。
- 後から変えられる: どの案も追加の Lean（または C は報告の形）なので、後で別の案へ移れる。D だけはコンパイラ変更を伴う。

## 7. 根拠

| 種類 | 内容 |
|---|---|
| 反駁の Check | `Tests/Gen5/CVTopCheck.lean` @40b176fe（par/cvtop、土台 f9dbc699）: `cvTop_not_functional`、`fgG_refutes_outer`。Job `kjob-run-src-cvtop-8246` exit 0、axioms 標準のみ |
| 空の関係 | `Tools/ShippingGen5DeclConnect.lean`: `ConstValueRel` :267、`DeclConnectAt` :274、`declConnect_eq` :281、`not_declConnect_of_empty` :291 |
| 関数性 | `Tools/ShippingGen5FG.lean:22`（定義）、`Tools/ShippingGen5DeclConnectAbs.lean:64` `dcImp_of_dcGen`（唯一の使用箇所） |
| 最終の文 | `Tools/ShippingGenFGLedgerPremisesG.lean:74`（`CV` binder、D.D-4）、:82（結論 `ConstValueFunctional CV ∧ …`） |
| 規則の分類 | `scripts/gen5/DC_CONNECT_FREEZE.md` rev5 §C.6（l.452-487）、`CV := ConstValueE …` の方針（l.388-391） |
| 選択肢 | `scripts/gen5/DC_CONNECT_PRIM_TABLE_DECISION.md` rev5 §3（A〜D）、§4（推奨）、§5（可逆性・未測定項目） |
| 台帳 | `scripts/gen2/premise_ledger/D_M5t2.md` D-4（l.352-363、`seq3553`）。`scripts/gen2/PREMISE_LEDGER.md` §12.22 は worktree の HEAD には無く、`par/fg-ledger-sync` bac6a3ac で読んだ（FG 77 / T1 57） |
| 保証の規則 | `scripts/gen2/GENERAL_SPEC.md:488-507`（G3-DECL、M5 完了条件、(i) 条件付き結果への変更はユーザー判断） |
| 宣言ごとの今の対応 | `Tools/Prototype/DGenStored.lean:14-18`（カーネルが構成子の項をそのまま読むというメタ事実は「NOT FORMULATED」、不可能とは主張しない） |
