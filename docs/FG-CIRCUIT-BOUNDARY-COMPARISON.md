# FG 回路パイロット: 境界の比較資料（案 2 の具体化）

Issue `sparkle-fg-circuit-pilot`、S3o。土台 `43a40e05`（S3n）。**未採用の比較資料。まず reviewer が確認し、その後にユーザーへ渡す。** 新 TRUSTED の採用・全面 E1 移植（案 1）の開始・v12 の作成はしていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

**【S3p 更新】** (c) の部分（§5.4・§6・§7）は S3p（`docs/FG-CIRCUIT-PILOT.md` §66、土台 `59a49445`）で更新した。更新箇所は「S3p」と明記した節と、各節末の「S3p 更新」の段落。S3o の本文は書き換えていない。S3p の結論は §6 末の「S3p: 再比較」。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

**【S3q 更新】** reviewer 裁定（S3o 後）の資料修正を反映した（`docs/FG-CIRCUIT-PILOT.md` §67）。変更点: (1) 受入範囲の明記（§4.8: 小モデル・仮説付き橋の成果であり、CorrE の実ランタイムでの充足や `Laws`/`CellPrem` の供給ではない。`Toy.RelT` と実 `RelE` の差、`EnvCorrE` の残る強さ）、(2) §3 の「証明も反証もできない」「道がない」を「調査範囲で未供給」へ、(3) §5.1 に既存 `machine_*` の実際の型の分類（ソース端点と run 付き shipping 定理の区別）、(4) §5.4 を古い CD/CDX と現行 CDT の混同を除いて書き直し、(5) §6 の (c1)/(c2) を「完成後の見込み」と「現時点の欠け」に分離、(6) §5.11 に S3q の M5・M1 の調査結果。(c) の最小試作の設計は §67（実装なし）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

**【S3s 更新】** reviewer の変更要求（`docs/FG-CIRCUIT-PILOT.md` §67.9）を反映した。変更点: (1) §5.10 の「純粋 builder は無い／`pureBuild` は書けない」を「調査範囲で既存定義を未発見、新実装は可能」に訂正し、(c) の鍵は純粋 builder ではなく **validator（`CheckRoot`）の健全性**と明記、(2) fallback の訂正（検査が false だった同じ artifact を返す fallback は不可。拒否、または同じ `S` について別に証明済みの fallback artifact を返しその枝も健全性に含める）、(3) CDT は run-free だが**無条件ではない**（`hftObCDT_T` の `EnvDefs`／`EnvCtors`／`RecFact` と実 env との対応、§5.4）、(4) 歴史的な「未確認 4 点」と旧 CD／CDX の結論を現在の要約で上書き（§5.4・§5.10）、(5) IR 返却形 → 最適化形 → SV 意味の 3 段の分離と、`combStmtI` の確定（assign／inst のみ true、register は false。17 register の top への `hier_pipeline_transfer` の直接適用は範囲外。§5.11）、(6) ソース束 `SourceData`／`RootShowsAt` の設計（§5.12）。**この資料は比較を示すもので、(a)／(b) の TRUSTED 採用を今求めない。** 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

この資料の各数値と主張は、(i) 今回 kernel / Check55 で確かめたもの、(ii) リポジトリのファイルを読んだもの、(iii) 未検証（coder の見積り・推測）のどれかを明示する。(iii) を (i) の言葉で書かない。

## 0. 先に結論

1. **S3n の橋の `EnvCorr` は実 `getEnv` の成功 run と両立しなかった（kernel で反駁）。** 旧 `InitCorr`/`quietR` は**全 world で成立**し、実プロセスの quiet を何も制限していなかった。修正版 `RelE env`（環境を明示的な oracle `env` として run 全体で固定）は、その反駁に当たらず、モデル内（toy 意味論）で全仮説と成功 `getEnv` が同時に成り立つ。これは**モデル内の事実**で、実 pilot の証人ではない（`docs/FG-CIRCUIT-PILOT.md` §65）。
2. **修正しても (b) は「未証明の文を小さくした」とは言えない。** `RelE` は世界の量化範囲を狭めない（任意の `w` に対し、`w` から読み出した `h` が `RelE` で関係する。§3.2）。変わるのは文の中身（世界の等式 → 値の文）と、見える単位（leaf 操作）だけで、各 leaf の対応仮説は不透明な実 primitive についての**未供給の文**のまま残る。
3. **最短経路の暫定の読み（未検証）**: このパイロットの root `synth_hftPcieOutByte` は machine 経路（`machineShape?` = some、instance 2、slot 17、S1 §14.4 SNAPSHOT8b）にあり、(c) の「生成物を kernel で検査する」経路が、`Laws`/`CellPrem` の完成を要さない唯一の案である。ただし (c) が成り立つかの**主要な未確認が 4 つ**あり（§5.4）、それを小さい調査（実装でなく、既存の生成器が pilot root に適用できるかの確認）で先に潰すのが、(b) の全面移植より安い。推奨ではなく reviewer の判断材料である。
   **S3p 更新**: 主要な未確認 4 つは確定した（§5.10）。2（純粋な組立関数）は**調査範囲で既存の定義を未発見**（新実装は可能。S3s 訂正）で、この項の「(c) が唯一の案」という暫定の読みは**弱まった**。(c) の IO を仮定しない形（(c1)）は成り立ち得るが、新規部品（返された module を検査する validator）が (b) と同じ桁になる可能性があり、(b) より安いとは言えない（§6 末）。

4. **S3q（reviewer 裁定の反映）**: (b) の成果の受入範囲は「小モデル・仮説付き橋」で、実ランタイムでの充足ではない（§4.8）。(c) は FG への正当な候補（元ソースの意味を出力から定義せず、ソース宣言/値と同じ返却 Module・Design の意味保存を kernel で証明する形）。ただし 1 artifact の証明書は局所成果で、現行 FG 全体の達成・全行減算にはしない（§5.7・§6）。root の返却 module は**未最適化・未 merge の raw そのもの**で（§5.11）、(c1) が検査する対象は出荷される（最適化後の）Verilog の元の module と同じ値である。

## 1. 共通の土台（S3n/S3o で確かめた事実）

| 事実 | 出所 |
|---|---|
| v11 `HftFinalStmtOffCombined11` は 10 binder（`L hquiet hsynth hr hcell hD hG hT hs h0`）の下の定理で、結論は `PostRunOff` と `RootArtifactMonoV`（元ソースの意味と返された `(b, D')` の対応）。`hr` は `pilotEntry3 hftRoot` の run。 | `Tools/ShippingFGCircuitS3kFinal.lean` |
| `CellPrem` は 10 conjunct = 16 atomic、`Laws` は `O` 10 field + `T` 4 field。非空虚な値は、既存の opaque IO 定義の上では構成できなかった（最初の阻害は `ReadWorld sparkleChildCache` と `diag` の `StderrKeeps`）。矛盾は見つかっていない。 | docs §63 |
| root は machine 経路: `certifiedShape?` = none、`mixedCertifiedShape?` = none、`machineShape?` = some（insts = `httpGetByte`, `tlpCplByte`、slots 17、runs 3、loops 0）。 | docs §14.4 / SNAPSHOT8b（プローブ `hftOutProbe` での測定。private な元定義そのものではない） |
| 台帳の行: A.P-01 = `Laws`（TRUSTED 候補。B.F-3, D.E-10 を併合）、A.P-02 = `Start`（`AdmCtx`。A.P-03, C.RR-1, B.F-2, D.E-11, D.D-6 を併合）、C.EN-4 = `CellPrem`（TRUSTED にするかは DG_ENV_FREEZE §4 の A/B/C 判断で、その記録は台帳調査で見つからなかった）。 | `scripts/gen2/PREMISE_LEDGER.md`（`8649968e`）。`hD hG hT hs h0` の行 ID は今回読み直していない |
| 戦略 §3.4・§5・§6: 証拠検査失敗は成功扱いにしない／「既存生成器が証拠を出し、小さい純粋 checker で検査」は採用方向／root で同じ環境・ソース・パラメータ・生成物を結ぶ。 | `docs/FG-CIRCUIT-STRATEGY-2026-11-06.md` |

## 2. S3n モデルと実 run の差分（案 2 の対象範囲を、操作の種類と量化範囲で）

S3n/S3o のモデルは 3 追跡 ref（`C`/`S`/`Nat` の型付き）、`mref`/`cref`/side の 3 位置（**3 つとも型 `Nat`**）、診断出力と環境変数の成分、leaf 3 種（`getStderr`/`getEnv`/`eprintln`）と `get`/`set` だけを持つ。実の `pilotEntry3` との差分:

| # | 実側の操作 | モデルの扱い | 対応に要る「操作の種類」 | 量化範囲 | 状態 |
|---|---|---|---|---|---|
| 1 | `mref : ST.Ref Meta.State`、`cref : ST.Ref Core.State` の get/set/modify | **`Nat` の位置**（実の状態型ではない） | 型 `Meta.State` / `Core.State` を持つ cell。`Sig.O` は 1 型なので **`Sig` の拡張（型付き other cell）が要る** | 全 `Meta.State`/`Core.State` の値。state の中身（env、cache、…）が他の操作に読まれる | 未モデル化。`ShippingHeapModel` の `Sig` 変更が既存の文を保てるか未確認 |
| 2 | `SideRef`（24）の get/set/modify/modifyGet | `other n` の位置はあるが実との `Rel`・`Corr` なし | 24 ref × 4 操作。各 ref の型が異なる（`Nat`、`HashMap`、…） | 全値 `v : σᵢ` | 未モデル化（#1 と同じ型の問題） |
| 3 | 新しい ref（`IO.mkRef` と `Fresh`） | `alloc` はあるが実の `mkRef` との対応なし | 実 ref の同一性（`ST.Ref.ref` の別個性）とモデル位置の**単射な対応**。`r.ref ≠ cref.ref` は `ST.RefPointed.type` の相異なる 2 点を要し、調査範囲で未供給（§63.3） | 全ての新規 ref。実行ごとに増える | 未モデル化。**本質的に新しい仮定が要る可能性**（相異なる ref の存在） |
| 4 | 例外（`throwError`、`try/catch/finally`、`Throws` 2 構成子、`OkExc`/`OkEnv`/`OkMsg`） | `.error` の出口はあるが橋では未使用。S3n の `Corr` の向きは「実成功 → モデル成功」で、実の失敗を扱わない | `try/catch` の対応は**失敗側**の対応（実の例外値とモデルの例外の関係）を要する | 全ての `Exception` 値（Lean の `Exception`、`MessageData` 付き） | 未モデル化。向きの拡張が要る |
| 5 | Meta primitive（`whnf`、`inferType`、`getConstInfo`、Meta の `getEnv`、`readThe`、`ppExpr` …、十数個） | なし | 各々が `Meta.State`（キャッシュ）を変更し得る。追跡 3 ref とモデルの診断成分を保つ文（`Laws.frame`/`frameQ` の相当） | 全ての `Expr`、全ての `Meta.Context`/local context | 未モデル化。**`Laws.frame` と同じ全称量化が残る**（restate するだけ） |
| 6 | telescope（`lambdaTelescope` 等 4 行）、`localDecl`、`letDecl` | なし | **高階**の対応: 継続 `k : Array Expr → Expr → MetaM α` ごとに、継続の対応が要る。local context が run 中に変わる | 全ての継続 `k`（量化が関数に及ぶ） | 未モデル化。`corr_bind` の高階版が要る |
| 7 | `Diag` の他の構成子（`profLog`、`ppExpr`、`ioEprintln`、`msgToString`、`stderrFlush`、`ioHandleMk/PutStrLn/Flush`） | `eprintlnM` と `getStderrM` のみ（ストリーム値は比較しない） | `Handle` を持つ操作は**任意の `Handle`** を含む（`Laws.O.diag` は全 `Handle`） | 全 `Handle`、全 `MessageData`、`stream callback` | 未モデル化。**`SPARKLE_PROFILE`・`DEBUG_HWCALL`・stream callback の安全性は、このモデルの `SPARKLE_DEBUG` の例から何も出ない** |
| 8 | 環境変数（`IO.getEnv`、`quiet` の実体） | `DiagEnv.env`（oracle `env`）の lookup。**quiet はキー `SPARKLE_DEBUG` のみ** | `quiet` が実際に何の事象の不在かは `Laws.O.quiet`（抽象 field）で、モデルの `quietM` は 1 キーの不在という**具体化の一例**にすぎない | 環境が run 中に変わらないこと（oracle 固定）。`IO.setenv` を compiler が呼ばないことは**今回確認していない** | oracle 固定は修正版で明示。他の環境キーは未モデル化 |
| 9 | 結合子（`ite`、`match`、`try/finally`、`for`、`partial` 再帰、`synthesizeChild` の相互再帰） | `pure`・`bind` のみ | `for` は帰納、`partial`/相互再帰は fuel または well-founded な測度（`depth` が測度か否かは**未確認**） | 全ての反復回数・全ての再帰深さ | 未モデル化 |
| 10 | `hr` を `pilotEntry3` のモデル run に落とす（run 全体の分解） | `bridge_small`（4 leaf）のみ | 数百の leaf への分解（S3m: 数百の opaque IO） | 全 run | 未構成 |

## 3. 案 (a): 現行の `Laws`/`CellPrem` のままの条件付き保証

### 3.1 未証明の文（そのまま）
v11 の 10 binder が未供給: `L : Laws mref cref`（14 field）、`hquiet : L.O.quiet w`、`hsynth : sv w = some synthesizeChild`、`hcell : CellPrem MkRefd mref cref`（16 atomic）、`hD`、`hG`、`hT`、`hs`、`h0`、および `hr`（run の成功そのもの。これは前提であって未証明の文ではない）。S3m の調査では、`hcell` の第 1 field `ReadWorld sparkleChildCache`（`∀ w, getW r w = w`、**全 `w : Void IO.RealWorld`** 上）と `L.O.diag`（`StderrKeeps quiet`）が最初の阻害。これらは、S3m の調査範囲では既存の opaque な IO 定義の上で供給（構成）も反証もできなかった（opaque であること自体が不可能性の証明ではない）。非空虚性（同時充足）は未確認で、矛盾も見つかっていない。

### 3.2 利用者への保証
「`pilotEntry3 hftRoot` の run が成功して `(b, D')` を返し、上の 10 前提が成り立つなら、その同じ `(b, D')` が元ソース `hftRoot` の意味を持つ（`RootArtifactMonoV`）」。**同じ元ソース・同じ返された artifact**（`hr` が結論の `b D'` を決める）で、IR の型検査ではない。ただし前提が実プロセスで成り立つことは**証明も検査もされていない**ため、利用者への無条件の保証ではない。

### 3.3 保つ IP
全て保つ（コンパイラ不変。出力の変更なし）。

### 3.4 残る台帳行
A.P-01、A.P-02（`hr` の検査で一部）、C.EN-4、`hD hG hT hs h0` の行。FG 75 / T1 57 のまま（減らない）。

### 3.5 操作の種類と量化範囲
`Laws.O.diag` は全許容文脈・全 `Diag p`（任意 `Handle`）・全 quiet world。`CellPrem` は全 world。全 `Expr`、全 `Meta.Context`（`frame`）。

### 3.6 費用
追加費用 0。ただし (a) のままでは、前提の充足可能性は調査範囲（S3m）で示せていない（不可能と示したのではなく、未供給）。

## 4. 案 (b): 修正版 Corr（明示状態・oracle 固定）の保証と、実 IO に残る対応

### 4.1 今回の修正（kernel 済。`Tools/ShippingFGCircuitS3oFix.lean`）
- 反駁: `envCorr_inconsistent`（旧 `EnvCorr k` + 実 `getEnv k` の 1 つの成功 run で `False`。`hEmpty`（env = `[]`）と `hSome`（env = `[(k,"v")]`）が同じ `w` に旧 `Rel` で関係し、同じ実戻り値 `a` が `none` と `some "v"` の両方に等しくなる）。実 run は任意の world から必ず存在する（`runsTo_getEnv`、`BaseIO`）。
- 反駁: `oldInit_any_world`（旧 `InitCorr w ∧ quietR w` が任意の `w` で成立）、`oldQuietR_eq_true`（`quietR = fun _ => True`）。
- 修正: `RelE env h w := cv w = h.cache ∧ sv w = h.synth ∧ dv w = h.depth ∧ h.reg.env = env`。`CorrE env`、`GetCorrE`/`SetCorrE`/`StderrCorrE`/`EnvCorrE env k` を oracle `env` に対して再記述。oracle は `corrE_bind` の仮説・継続の仮説・結論のすべてで**同じパラメータ**で、leaf ごとに選び直せない。`corrE_bind`、`bridge_smallE`、`real_small_consequenceE` を再証明。同一 oracle の 2 回読み `bridge_env_twice`/`real_env_twice`（両方の読みが `lookupEnv env k`）。
- 対照: 旧 shape が許した「環境の異なる 2 状態が同じ world に関係する」ことは `relE_not_both`（同じ oracle では不可）で拒否。oracle が `k` 未設定なら実の観測 `some v` は不可（`envCorrE_observation_committed`）。
- 同時充足（**モデル内**。範囲は §4.8）: toy 意味論で、1 つの oracle・1 つの開始 world・quiet なモデル heap・全 leaf の対応・合成プログラムの対応・成功 `getEnv "HOME"`（`some "/root"`）が同時に成立（`Toy.simultaneous_sat`）。

### 4.2 修正版が実 world について**制約すること／しないこと**
- `InitCorrE env w0 ↔ lookupEnv env "SPARKLE_DEBUG" = none`、`quietRE env w ↔ 同じ`（`initCorrE_iff`、`quietRE_iff`）。**world に依存しない**（`quietRE_world_independent`）。制約するのは **oracle `env`** であり、実プロセスの環境との接続は `EnvCorrE env k`（実 `getEnv k` は `lookupEnv env k` を返す）の仮説**だけ**が担う。
- 制約**しない**もの: `SPARKLE_DEBUG` 以外のキー（`SPARKLE_PROFILE`、`DEBUG_HWCALL` など）、stream callback、`Laws.O.quiet` の抽象 field 全体（`quietRE := Laws.O.quiet` となる `Laws` は作っていない）、出力成分 `stderr`、`mref`/`cref`/side ref。環境が run 中に変わらないこと（oracle 固定）は**仮説の内容**であって証明ではない。
- `EnvCorrE env k` は全 world `w`（`RelE env h w` を満たす `h` がある `w`）で実 `getEnv k` が同じ値を返すと言う。**`RelE` は世界の量化範囲を狭めない**: 任意の `w` に対し `h` を `w` から読み出して `RelE env h w` が成り立つ（`heapOf` と同じ作り）。言い換えは文の中身（`getW r w = w` のような世界の等式 → 値の文）であって、対象 world の絞り込みではない。

### 4.3 未証明の文
- 各 leaf の `GetCorrE`/`SetCorrE`（追跡 3 ref、side ref 24、`mref`/`cref`、fresh ref）、`StderrCorrE`、`EnvCorrE env k`（環境キーごと）、未定義の例外・Meta primitive・Handle・telescope の `CorrE`。いずれも実の opaque primitive（`ST.Prim.Ref.get/set`、`IO.getStderr`、`IO.getEnv`）についての文で、モデルでは証明されない。
- 初期対応 `InitCorrE env w0`: `lookupEnv env "SPARKLE_DEBUG" = none` と同値（上記）。
- v11 の `hcell hD hG hT hs h0 hquiet hsynth` を `RelE` の像の上の文へ書き直す v12 の再定式化（成り立つかは**未確認**）。
- `hr`（`pilotEntry3` の run）のモデル run への分解（§2 #10）。

### 4.4 利用者への保証
「oracle `env` と上の leaf 対応が実プロセスで成り立つなら、`pilotEntry3 hftRoot` の成功 run が返す `(b, D')` は元ソースの意味を持つ」。**同じ元ソース・同じ返された artifact**（v12 の結論が v11 と同じ `(b, D')` を対象にする場合）。ただし v12 は未作成。(a) との違いは仮説の形（世界の等式 → 値の文）と局在（leaf 操作ごと）で、**仮説が調査範囲で供給されていないことは (a) と同じ**。

### 4.5 保つ IP
全て保つ（コンパイラ不変）。

### 4.6 残る台帳行
A.P-01、C.EN-4 は、leaf 対応仮説の集合に**置き換わる**だけで、供給されない限り（調査範囲では未供給）減らない。置換後の行数は、操作の種類（§2 の 10 行）に比例し、現時点では**数えていない**（FG 75 は不変）。新 TRUSTED の候補になる（採用していない）。

### 4.7 費用
- coder の見積り（**未検証**）: 全体で 2,500〜4,000 行（S3n 小接続 約 300 行を、`SideRef` 24、`Diag` 残り 8、Meta primitive 十数個、telescope 4、例外、`mkRef`、`modify` へ、leaf あたり 30〜60 行で拡張）。
- 既知の部分（テンプレートが今回までにある）: 追跡 ref の `get`/`set` の `Corr`（`getCorrE_of_readWorld`、`setCorrE_depth`）、`pure`・`bind`（`corrE_pure`/`corrE_bind`、型 ~20 行）、診断 leaf（`getStderr`/`getEnv`/`eprintln` の model 側の保存補題）、同一 oracle の合成。今回の実測: 修正（反駁・`RelE`・bridge・toy・同時充足）で `Tools/ShippingFGCircuitS3oFix.lean` 433 行（反駁と toy を含む）、Check55 195 行。
- 未知の部分（テンプレートがなく、行数を見積れない）: §2 の #1（`Sig` の型付き other cell 化と `ShippingHeapModel` の既存文の保持）、#3（fresh ref の単射対応と相異なる ref の存在）、#4（失敗側の対応）、#6（高階の telescope）、#9（`for`・`partial`・相互再帰の測度）、#10（`pilotEntry3` の run 全体の分解）、v12 の再定式化が成り立つか。**2,500〜4,000 行は既知部分の外挿であり、未知部分を含まない**。

### 4.8 受入範囲（S3q、reviewer 裁定）: 何を受け入れ、何を受け入れないか

**受け入れるもの**: 小モデル・仮説付き橋の成果（反駁 2 件、修正版 `RelE env` と `corrE_bind` 等、モデル内の同時充足）。**受け入れないもの**: `CorrE` の実ランタイムでの充足、`Laws`/`CellPrem` の供給。

**`Toy.RelT` と実 `RelE` の差**: `Toy.RelT env h w` は world 側に環境成分 `w.penv = env` を持つ（toy の world が環境を持つ）。実 `RelE env h w` は `cv w = h.cache ∧ sv w = h.synth ∧ dv w = h.depth ∧ h.reg.env = env` で、**実 world `w`（`Void IO.RealWorld`）の環境に何の制限も置かない**（§4.2）。したがって `Toy.simultaneous_sat` は「`GCorr` の toy 解釈の充足」であり、**実の `RelE`/`CorrE` 一式の整合性証明ではない**。実 `RelE` で同じ 7 項目（oracle・開始 world・quiet な heap・全 leaf の対応・合成・成功 `getEnv`）が同時に成り立つかは未確認のまま。

**残る強さ（反駁を逃れたあと、`EnvCorrE` がなお要求するもの）**: 実 `RelE env` は**任意の `w`** に対して関連する heap を作れる（`rel_heapOf`）ので、`EnvCorrE env k` は「固定した oracle の値 `lookupEnv env k` を、**全 world** での実 `getEnv k` の成功が返す」ことを要求する。これは単に「ある run の間に環境が変わらない」より強い。**compiler が `setenv` を呼ばない、という事実だけでは供給できない**（全 world への量化が残る）。将来 (b) を実装する場合は、oracle と実 world の対応（許容 world または到達範囲）を別途の文として要る。**今この境界を TRUSTED として採用しない**。

## 5. 案 (c): 元ソースの意味と**返された IR** の対応を kernel で検査する証明・証明書（調査のみ）

コンパイラの IO 全体を正しいと仮定せず、**返された artifact という値**が元ソースの意味と一致することを、kernel で検査する（reviewer 裁定: FG への正当な候補。ただし 1 artifact の証明書は局所成果で、一般には checker の健全性 `∀ source artifact cert, check source artifact cert = true → 意味保存` と、採用入口が検査した同じ artifact だけを返す接続が目標。IR の証明・SV 文字列の一致・SV の意味保存を区別し、ハッシュ一致だけを kernel 内の意味保存と呼ばない）。戦略 §5 の「既存生成器が証拠を出し、小さい純粋 checker で検査」に当たる。**新規の全面実装はしない。以下は候補調査で、成立は未確認。**

### 5.1 リポジトリに既にあるもの（ファイルを読んで確認）
- **`#machine_endpoint f`**（`Tools/ShippingMachineCommand.lean`）と `machine_trace_of_data`（`Tools/ShippingMachineAuto.lean`）: 元の宣言 `f` の本体を `MachineData` に読み、`MachineData.ok`（全 side condition の 1 つの Bool）と 5 つの等式を `Eq.refl` で kernel 検査して `f.machine_sound : MachineTrace …` を生成する。コーパス 120 宣言で生成済み（`docs/ShippingCompiler-Coverage.md`）。**元ソース側の kernel 検査は既にある。** `unq` は意図的に未検証で、等式の kernel 検査が受理の根拠。
- **ただし生成される `f.machine_sound` の前提は run**: `synthesizeCombinationalCore_machine_sound` は `hr : RunsTo (synthesizeCombinationalCore declName [] false) … (m, d) w'` と `MachineDefines`・`MachineCloses`（run がこの shape を読んだ／`let` を結んだ）を取る（`Tools/ShippingMachineEntry.lean:2388`）。FG の証明では `MachineDefines` を `Laws`・`hquiet`・`GetEnvFrame` から供給する（`machineDefinesLinked_of_env`、`Tools/ShippingFGCircuitLinked.lean`）。つまり**現行の machine 経路の端点は IO run を経由し、(c) の「IO を仮定しない」形ではない。**
- **返された module に対する純粋な decidable 検査と kernel 済の健全性**: `refineCheck`（`Sparkle/IR/RefineCheck.lean`）+ `refineCheck_transfer`（`Tools/ShippingRefineSoundness.lean`）、`EmitSem.seqCheck`（出力 Verilog の検査）。checker とは別に、shipping 定理 `machine_ships`/`machine_ships_checked`（`Tools/ShippingMachineShipping.lean`）、`machine_ships_wired`（`Tools/ShippingMachineShipsW.lean`）、`machine_ships_comb`（`Tools/ShippingMachineShipsComb.lean`）がある。**これらの shipping 定理は全て `hr`（`synthesizeCombinational` の run）と `MachineDefines`/`MachineCloses` を取る run 付きの定理**で、純粋 checker ではない（`hierRefineCheck` 等の checker を前提の一部に使う）。コーパスでは 113 の machine 経路宣言のうち 107 で全 gate が成立し 6 が `seqCheck` で棄却（`docs/ShippingCompiler-Coverage.md`）。コンパイラ自身も `mergeChecked`/`checkedOptimize` で `refineCheck` を呼び、棄却時は未 merge／未最適化の module を返す（検査失敗を throw にはしない）。
- `machineShape?` は純粋関数（同文書）。

#### 5.1a root の `machine_*` 定数: 名前ごとの実際の型（S3q [プローブ]: 型の読み出しと、型に `RunsTo` が現れるかの検査。1 環境・この base）

root `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte` 名前空間の定数は 21 個（def 9、theorem 12）。**型に `RunsTo` が現れるのは `machine_sound` ただ 1 つ**。

| 種類 | 名前（実際の型） | run を含むか |
|---|---|---|
| ソース端点（定数 `R` そのものについての文。`Eq.refl`/`decide` で kernel 検査済み） | `machineData : MachineData`、`machine_ok : machineData.ok = true`、`machine_body : machineData.shape.body = quote …`、`machine_inits`（`initOk …`）、`machine_writes`（`∀ i bools bits S Ss t, …`）、`machine_result`（`∀ i bools bits S Ss, …`）、`machine_source : ∀ i bools bits, machineSource i bools bits = machineResult i (resOn (fusedBody …))`、`machine_states : ∀ i bools bits, ∃ S₂ Ss, teleState … ∧ …`、`machine_arg_0/1`・`machine_inst_0/1`（呼び出しごとの引数・状態の事実。`∀ i bools bits S Ss, …`） | 含まない |
| ソース側の定義（def） | `machineSource : Unit → (Nat → Signal Bool) → (Nat → (n : Nat) → Signal (BitVec n)) → List (Nat → Nat)`、`machineBody`・`machineResult`・`machineInits`・`machineInners`・`machineExt`・`machineCall_0/1` | 含まない |
| run 付き（IR 側への端点） | `machine_sound : RunsTo (synthesizeCombinationalCore R [] false) mctx mref cctx cref w (m, design) w' → MachineDefines … → MachineCloses … → MachineTraceWith …` | **含む**（`hr`・`entry`・`closes`） |
| scratch で生成して確かめた run 付き | `#machine_linked` → `machine_linked`、`#machine_composed` → `machine_composed`（どちらも 11 binder: `mctx mref cctx cref w w' m design hr entry closes`、S3p §66.3） | 含む |
| root には**生成されない**もの | `machine_closes`、`machine_ships`・`machine_ships_wired`・`machine_ships_comb`、`machine_composedT*`、`machine_ships_hier`（理由は §5.10 の 1） | — |
| 子（`httpGetByte`・`tlpCplByte`）に生成されるもの | `machineData`・`machine_ok`・`machine_body`・`machine_closes`・`machine_sound`・`machine_ships_comb`（`#machine_endpoint` のプローブ） | `machine_sound`・`machine_ships_comb` は run 付き |

**混同しないこと**: 「ソース端点」（`machine_source`・`machine_states` 等）は run を含まず、run 付きの `machine_sound`/`machine_linked`/`machine_composed`/shipping 定理とは別物。(c) の「元ソースの意味」に使えるのは前者で、IR 側の対応（`MachineTrace` 等）を与えるのは後者（run 付き）。**IR 側の対応を run なしで与える文は既存にない**（それが §5.4 の 2）。

### 5.2 pilot root の証明書に含まれるもの（案）
1. **返された artifact そのもの**: `pilotEntry3 hftRoot` が返す `(b, D')` を 1 回のコンパイル実行からシリアライズした**閉じた Lean 項** `(b₀, D₀)`（top と子 module `httpGetByte`・`tlpCplByte`）。
2. **元ソースの端点**: `synth_hftPcieOutByte`（公開版 `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte`、private な元定義ではない）の `MachineData` と `MachineData.ok`、5 つの等式（`rfl`）。
3. **artifact とソースの接続**: `MachineTrace data b₀ D₀` に相当する kernel 検査可能な命題。**これを `hr` なしで得る方法は既存にない**（既存の `machine_trace_of_data` の結論は「run が返した module」について）。必要なのは、module を `data` から組み立てる純粋関数（または module と `data` の対応を判定する純粋 checker）と、その健全性定理。
4. **出荷物の同一性**: 出荷される Verilog が `emit D₀` と一致することの検査（`emit` は純粋）。
5. **子 module の接続**: `D₀` の各 module が自分の宣言に対して検査され、instance の参照先が `D₀` に存在し名前が一意であること（Design の整合）。

### 5.3 同じ artifact を固定するか
固定する。ただし条件付き: 証明書は**記録した 1 回の出力**について成り立つ。コンパイラの変更（配線番号付け、`machCanonAp` のような名前の正規化。実際に `fsmHoldCdo` の配線番号が 1 つ変わった例が `Coverage.md` にある）で出力が変われば**再生成が要る**。「全ソースについてコンパイラが正しい」という一般定理ではなく、「このソースとこのバイト列」という artifact 固定の保証になる。IR の型検査ではなく、**観測（trace）の一致**を言う。

### 5.4 S3o の「主要な未確認 4 点」— S3p/S3q 時点の状態（S3o の原文を訂正）

**【S3s: 現在の要約。以下の歴史的な記述（旧 `CD`／`CDX` の結論、「未確認 4 点」）はこれで上書きする】**
| 点 | 現在の要約 | 旧い記述 |
|---|---|---|
| 1 `#machine_endpoint` | root に適用済み・通る。生成物は `machine_sound` まで run 付き | 未確認（superseded） |
| 2 純粋な組立関数 | 調査範囲で既存定義を未発見。新実装は可能。鍵は validator の健全性 | 「ない／`pureBuild` は書けない」（superseded） |
| 3 子の接続 | 既存は run 付き。run なしの文は `RootShowsAt` の ChildFn 連言として新規（§5.12） | 未確認（superseded） |
| 4 ソース側 | 現行は `CDT`（`cdvT`）。`hftObCDT_T` で導出は閉じているが**無条件ではない**（下） | 「`CD` に規則が無く導出は作れない」「`hcd` 未完了」（superseded。旧 `CD`／`CDX`／`CDY`／`CDZ` の経過） |


S3o の原文の 4 点のうち、1・3 は §5.10 で確定済み（root に `#machine_endpoint` は適用でき、子の接続の文は run 付きで既にある）。2 は「調査範囲で既存定義を未発見、新実装は可能」で確定（§5.10。S3s 訂正）。**4（ソース側）は S3o の原文が古い `CD`/`CDX` と現行の `CDT` を混同していた**ので、次のように訂正する。

- **古い（旧い導出）**: `CD`（`Tools/ShippingFGCircuit.lean`）には利用者定義定数と構造体射影の規則がなく、root の `CD` 導出は作れなかった。`CDX`（S1m）、`CDY`（S1p）、`CDZ`（S1r）はその拡張の途中経過で、当時 `hcd`（導出の供給）は未完了だった。S3o §5.4 の 4 はこの旧い状況を現在形で書いていた（誤り）。
- **現在（S2t・S2z の成果。現行 CDT）**: 現行の搬送は `CDT`（`cdvT`、表駆動、`Tools/ShippingFGCircuitS2iDT.lean`）。
  - `hftObCDT_T`（`Tools/ShippingFGCircuitS2tHftOb.lean`、S2t）: root の `HftObCDT env` を、`EnvDefs env Delta`・`EnvCtors env Gamma`・`RecFact env` の 3 条件の下で証明する定理（kernel 済み）。**`hcd` の導出は閉じている**。
  - S2z の表検査（`hftEnvCheckB`／`hftEnvCheckB_sound`、`Tools/ShippingFGCircuitS2zEnvCheck.lean`。`pin_defs`・`pin_ctors`・`startEnvOk_sound`、`Tools/ShippingFGCircuitS2zPin.lean`）: 決定可能な検査 `startEnvOk hftRoot env = true` が、**同じ `env`** で上の 3 条件を与える（kernel 済み）。
  これらは**現在の成果**であり、「未完了」ではない。
  - **ただし run-free であって無条件ではない（S3s）**。`hftObCDT_T env (hΔ : EnvDefs env Δ) (hΓ : EnvCtors env Γ) (hrec : RecFact env)` の前提: `EnvDefs`＝表 `Δ` の各行について `env.find? c = some (.defnInfo d)` かつ `d.levelParams`・`d.value` が行と一致（`Tools/ShippingFGCircuitS1mCD.lean:672`）、`EnvCtors`＝各行について `env.find? c = some (.ctorInfo cv)` かつ `induct`・`numParams`・`numFields` が一致（同 681）、`RecFact`＝`List.rec` の `recInfo` が `env` にある（`Tools/ShippingFGCircuitS1wTbl.lean:41`）。**実 env との対応**: これらは `Lean.Environment` の値 `env` についての文で、`env` が実際の環境であり表の行がその宣言と一致することは別に供給が要る。S2z の `startEnvOk hftRoot env = true`（決定可能検査）が同じ `env` についてこの 3 条件を与えるが、その `env` が kernel の定数 `R` の環境と同じであること（源環境・宣言の固定）は未解決。
- **(c) で再利用するために未解決の部分は、環境の対応だけ**: `hftObCDT_T` と表検査は **`Lean.Environment` の値 `env`**（run が読んだ `envAt cref w`）についての文で、(c1) の閉じた証明書は **kernel の環境の定数 `R`（`R.machineData`、`machine_source` 等）**についての文になる。(c) の「元ソースの意味」を `CDT` 側（`SourceDenotesMonoV … env`）と同じ義務として扱うなら、「`env` の `R` の定義値と、kernel の定数 `R` が同じ宣言である」という対応（源環境・宣言の固定）が要る。(c1) で元ソースの意味を kernel の定数 `R` の `machineSource` にする場合は、`CDT` を使わずに済むが、現行 FG の文面（`SourceDenotesMonoV` 形）とは対象が変わるので、新旧の差と消費者を示して正式に変更する必要がある（reviewer 裁定）。
- 残る S3o 原文の未確認（2：純粋な組立関数 — 既存定義は未発見、3：子の接続 — run 付き）は §5.10 の確定のとおり。

### 5.5 コンパイラの IO を仮定しないか
2 つの形があり、残る信頼が異なる:
- **(c1) オフラインの証明書**: 出力を Lean ファイルに書き出し、kernel が検査する。コンパイラの IO は**どこにも仮定されない**。残るのは「出荷物 = `emit D₀`」の突合（バイト比較またはハッシュ。kernel 内で `decide` するか、外部ツールかは**未決**）と、`D₀` を作った実行が出荷と同じ入力で行われたこと（運用手順）。保証は artifact 固定。
- **(c2) コンパイラ内の checker**: コンパイラが成功を返す前に純粋 checker を呼び、失敗なら throw する（戦略 §3.4）。checker の健全性は kernel 検査。残るのは「成功 run の末尾で checker が artifact に対して true だった」という **run の末尾の構造**の証明（`RunsTo.bind` の分解と checker の純粋性）で、`Laws`/`CellPrem` 全体は要らない見込み。ただし checker が読むソース環境が run 開始時の `envAt cref w` と一致する（env が run 中に宣言 `X` について変わらない）ことの frame が要り、**これが `Laws` 相当の frame を再び要求しないかは未確認**。

### 5.6 保つ IP
(c1) はコンパイラ不変なので全て保つ（出力変更なし）。(c2) は検査失敗を throw にするので、**以前成功した入力がエラーになり得る**（戦略 §5 の指摘）。現在のコンパイラは検査失敗時に fallback するため（`mergeChecked`）、throw に変えると必要 IP が落ちないかをコーパス（107/113）で再確認する必要がある。

### 5.7 残る台帳行
(c1): pilot root 1 件については A.P-01・C.EN-4 の行を通らない（run を使わない）。ただし FG の定義が「`compileCircuit … = .ok artifact` の全称の定理」（戦略 §6）なら、artifact 固定の証明書はその形の定理ではない。**reviewer 裁定（S3q）: 具体的な 1 artifact の証明書は局所成果として受理できるが、現行 FG 全体の達成・全行の減算にはしない**。一般には checker の健全性「`∀ source artifact cert, check source artifact cert = true → 意味保存`」と、採用入口が検査した同じ artifact のみを返す接続を目標にする。元の FG 文の対象/前件が変わるなら、新旧の差と消費者を示して正式に変更する。本資料は数を変えない。(c2): A.P-02 の一部と、末尾の frame の行。減る数は未見積り。

### 5.8 操作の種類と量化範囲
(c1): 量化は閉じた artifact 1 つと、`MachineData` の有限データ。全 world・全 run の量化は無い。(c2): checker の健全性は全入力で kernel 検査し、run 側は末尾の bind 分解のみ。

### 5.9 費用
既知: `#machine_endpoint` の 1 宣言あたりの kernel 検査は 0.1〜1.5 秒（`Coverage.md` の 55 宣言での測定）。`refineCheck` の吸収は既存。**未知（行数を見積れない）**: §5.4 の 4 点、シリアライズ（閉じた Lean 項への書き出し。巨大 module の kernel 検査の規模。CRC の正規形は 0.5〜0.75M ノード）、`emit` 突合の方式。調査自体（実装なし）の作業量: §5.4 の 1 と 2 を `kjob lake env lean` のプローブで確認する程度で、小さい。


### 5.10 S3p: §5.4 の未確認 4 点の確定（`docs/FG-CIRCUIT-PILOT.md` §66。読みとプローブ。実装なし）

出所の種類: **[読]** ファイルを読んだ、**[プローブ]** scratch での読み取り専用実行（1 環境・この base の値）、**[未]** 未確認。

1. **pilot root に `#machine_endpoint` は適用できるか — できる（S1k で適用済み）。** root には `machineData`・`machine_ok`・`machine_body`・`machine_sound`・`machine_states` 等 21 個の定数がある。**無い**ものは `machine_closes`・`machine_ships*`・`machine_composedT*`・`machine_ships_hier`。理由: `machine_ships*` は `Tools/ShippingMachineCommand.lean:2728` の `if r.shape.insts.isEmpty`（insts 付きは設計上出さない）、`machine_closes` はデータに呼び出しがあると作れない（`Tools/ShippingMachineClosesGen.lean:119` のエラー）、`machine_composedT*`／`machine_ships_hier` は `endpointParts`（`Tools/ShippingMachineSeqCommand.lean:71`）が root の頭 `machine_trace_of_tele_ext` を持たない（`no wired twin for its head`）。**`#machine_linked` と `#machine_composed` は root に通る**（[プローブ]）。ただし生成される `machine_sound`／`machine_linked`／`machine_composed` は全て `hr`・`entry : MachineDefines`・`closes : MachineCloses` を取る（run の 11 binder）。
2. **Module（と Design）を組む純粋関数はあるか — 調査範囲では既存定義を未発見。** 純粋なのは仕上げの `closeLets`／`closeMachine`／`closeInstsG` と後処理（`dropZeroWidthModule`／`mergeChecked`／`checkedOptimize`／`toVerilogDesign`）だけ。中核は `synthesizeMixedCertified`（`MetaM`、fresh な id と `IO.Ref` のキャッシュ）＋ translator（`CompilerM`、グローバル `IO.Ref`）。既存の健全性の文は `∃ ids cache, … MachineWired …` の存在形で、`m = build …` の等式ではない。→ **調査範囲では `src` から `M` を作る既存の純粋定義を発見していない**（`pureBuild src = M` の形の定義・等式は見つかっていない）。これは**新実装が不可能という意味ではない**: 新規に書くことは可能で、**(c) の鍵は純粋 builder ではなく validator の健全性**（返された module を検査する `CheckRoot` を任意の `S`・`b`・`D`・`cert` について健全に証明する。生成器は untrusted で任意でよい）。S3o／S3p の「`pureBuild` は書けない」は、この文で置き換える。
3. **子 instance の接続 — 覆うが run の仮定は外れない。** `machine_linked`（子は `ChildFn mc …` を仮定）、`machine_composed`（子は `MachineRun child shape mc`＝子の run の存在を仮定）はどちらも root の 2 つの子を扱うが、`hr`・`entry`・`closes` が要る。FG 側の鎖（`machine_ships_hierC_runOff`、`machine_linked_callsServed1` 等）も `L`・`hr`・`CellPrem` 由来の前提を取る。
4. **ソース側 — `CDT`（`cdvT`）が root で使え、導出は閉じている。** 「ソースの意味 = 返された IR の意味」を述べる既存定理は v11 `HftFinalStmtOffCombined11`（前提 10 binder: `L hquiet hsynth hr hcell hD hG hT hs h0`）。ソース側（`SourceDenotesMonoV`、`ObservationsEqualMono`）は環境 `envAt cref w` にだけ依存し、artifact 側（`HasConcretePackage`）が `hr` を要する。run なしの閉じた source 側の部品として `machine_states`・`machine_source`・`hftRootLink` がある（定数 `synth_hftPcieOutByte` そのものについての文）。

**この確定が (c) について意味すること**: 「`#machine_endpoint` が通るか」「接続の文があるか」という 1・3・4 は肯定的だが、いずれも run 経由。(c) を IO 非依存にするには、2 の既存の純粋 builder は調査範囲で未発見のため、builder を使わずに返された値を検査する。したがって (c1)（オフライン証明書）の新規部品は、返された module を `MachineData` に照らして検査する純粋 checker（validator）とその健全性になる（§66.6 の M1〜M8）。

### 5.11 S3q: M5（返された module と既存の検査器）と M1（演算の範囲）の調査結果（`docs/FG-CIRCUIT-PILOT.md` §67.1・§67.2。読みと scratch の読み取り専用プローブ。実装なし）

出所: **[プローブ]** scratch での読み取り専用実行（1 環境・この base `8b7953d1`、`pilotEntry3` を 1 回走らせた値）、**[読]** ファイルを読んだ。

**M5**:
- **root の返却 module `b₀` は raw そのもの**: `b₀ == raw`（`synthesizeCombinationalCoreOffR pilotReaderOk2` の出力）、`dropZeroWidthModule raw == raw`、`mergeChecked (dropZeroWidthModule raw) == raw`（merge 後処理は何も変えない）。`mergeDuplicates raw ≠ raw`（merge の候補はあったが採用されなかった）。理由は構造的: `mergeChecked_inst`（`Tools/ShippingMachineShipsHier.lean:69`、kernel 済み）が「inst を含む module では `mergeChecked` は入力をそのまま返す」を述べる（`refineCheck` は inst 文を持つ body を `seqStmtOk` で拒否する）。**最適化は返却の段階では行われない**: `checkedOptimize` は printer（`verilogOf`）で `b₀` に適用される別の純粋ステップ。
- 検査器の適用結果（[プローブ]）:

| module | `refineCheck m m` | `seqGate` | `hierGate`／`hierBinds` | `hierRefineCheck m m` | `shipsHierCheck (childMap D.modules) m` | 出荷される形 `checkedOptimize m` | `seqCheck`（出荷形、`moduleWof`） |
|---|---|---|---|---|---|---|---|
| top `b₀`（256 文: assign 237、register 17、inst 2） | **false**（inst は `seqStmtOk` でない） | false | true／true | true | true | **`b₀` と異なる**（89 文。`deinline` 後の候補を `hierRefineCheck` が受理） | true（幅の一致も true） |
| 子 `httpGetByte`（88 文、assign のみ） | true | false | false／false | — | — | `b₀` と**同じ**（optimizer の候補 7 文は不受理で入力を返す） | true |
| 子 `tlpCplByte`（159 文、assign のみ） | true | false | false／false | — | — | 同じ（候補 18 文は不受理） | true |

- 失敗する形: root の top に対する `refineCheck`／`seqGate` を前提にする検査・定理（`machine_ships`、`machine_ships_checked`、`machine_ships_wired`、`machine_ships_comb`: いずれも `insts = []` 等を要し、かつ run 付き。root には生成されない、§5.10）。通る形: `hierBinds`・`hierRefineCheck`・`shipsHierCheck`、`seqCheck`（出荷形）。
- **fallback の有無（reviewer: 最適化形を拒否して既証明の未最適化 artifact へ戻す安全な経路は禁止しない）**: (i) コンパイラ側の fallback は**既にある**: `mergeChecked`／`checkedOptimize` は検査に落ちたとき入力 module を返す（throw しない）。root の merge は実際にこの fallback で入力に戻っている。(ii) (c) が検査するのは `b₀`（未最適化の raw）なので、IR レベルでは「最適化形を拒否して戻る先」と `b₀` は同じ値で、**追加の fallback 実装は要らない**。ただし**「既証明」の未最適化 artifact は root の top には現時点で存在しない**（既存の全ての証明は run 付き。M1 が無いと `b₀` の意味保存は証明できない）。(iii) 出荷形（89 文）まで kernel で覆うかは別: 既存の `hierRefineCheck_linkedH`（`Tools/ShippingHierOptRunH.lean:412`、kernel 済み）が `hierRefineCheck m o = true` を前提に `b₀` から出荷形への移送を与えるが、設計側の前提（`linkedWF`・`kidsLocal`・`hOutM` 等）を要する。(iv) 代わりに root だけ最適化せず `b₀` をそのまま印字する fallback は**小さい**（`checkedOptimize b₀` を `b₀` に替える分岐 1 つ）が、**出力の SV テキストは今日と異なる**（top が 89 → 256 文。子は同じ）。出力が変わるので **IP のベースラインのテキスト比較は変わる**（意味が同じでも文字列は同じでない）。範囲を root に限らず全 module に適用すると全 IP の出力が変わるので、適用するなら対象を限定する。

- **【S3s: fallback の規則】** 検査が false だった**同じ artifact を返す** fallback（「拒否の代わりに `pure (b, D)` を残す」）は不可（`certifiedReturn_sound` が破れる）。許されるのは (1) 拒否、(2) 同じ `S` について**別に証明済みの** fallback artifact を返し、その枝も健全性の結論に含める形。現在のコードに未実装。上の (i)(ii) の既存 fallback は検査の通らなかった最適化形を捨てて raw を返すもので、(c) の新しい `certifiedReturn` の fallback とは別。
- **【S3s: 3 段の分離】** ① IR 返却形（raw `b₀`）の意味 → ② 最適化形（出荷形 89 文）との対応 → ③ SV の意味、は別の義務で、**ある Check が true という測定だけでは移送済みにしない**。確定した事実: `combStmtI`（`Tools/ShippingHierSVSoundness.lean:404`）は `assign`／`inst` だけ true、`register` は false。よって**17 register の top への `hier_pipeline_transfer` の直接適用は範囲外**（旧文の「未確認」を置き換え）。上の表の top の `refineCheck` は false で、top は階層検査（`hierRefineCheck`／`shipsHierCheck`）で検査される（`refineCheck` が 3 module で true という読みは誤り。true は子 2 つ）。

**M1**（root の module が使う IR の形。[プローブ]）:
- **文の種類**: top = `assign` 237、`register` 17（全て clk・同期 `rst`・初期値 0）、`inst` 2（`httpGetByte`、`tlpCplByte`）。`memory`・assertion・parameter は無い。子 2 つは `assign` のみ（88 と 159）。
- **式の形と演算子**（top: ref 426、slice 66、concat 2 引数 64、mux 3 引数 42、eq 19、and 10、or 6、add 3、shl 2、const 25（全て非負））。子 88: ref 122、slice 13、concat/2 12、mux 17、eq 17、const 29。子 159: ref 255、slice 51、concat/2 42、mux 30、eq 15、const 21。**root 全体で使う演算子は `mux`・`eq`・`and`・`or`・`add`・`shl` の 6 種**（`sub`・`mul`・`xor`・`not`・`neg`・比較 `lt`/`le`/`gt`/`ge`（`_u`/`_s`）・`shr`・`asr`・`sliceDim`・`index` は無い）。
- 被覆（既存の純粋 checker／健全性の補題。詳細は §67.2）: 6 種の演算子と const・ref・slice・concat/2 の全てが (i) `refineCheck` の正規形（`rNormE`: `rBinOk` が `add`/`and`/`or`/`shl`/`eq` を含み、`mux` は `rMux`、`slice` は `rSlice`、`concat [a,b]`）に入る、(ii) 出荷形の `seqCheck`（`sf4Check`）を通る（[プローブ]）。IR 側の評価意味（`Semantics.evalOp`／`evalExpr`）は `add`・`eq`・`shl` ほか各演算子にある。**被覆されないもの**: 「`MachineData` の項から module の文への対応」を検査する純粋 checker は無い（これが M1 そのもの）。run 側の lowering の補題は `add`/`and`/`or`/`shl`（`Binary.emit_correct`、`Tools/ShippingScalarSoundness.lean`）、`mux`（`emitMuxResult_correct`、`Tools/ShippingMuxLoweringSoundness.lean`）、比較（`Tools/ShippingCompareLoweringSoundness.lean`、`eq` がこの種別に当たるかは名前でしか確かめていない）にあるが、`slice`・`concat` の lowering の補題は名前検索で見つけていない（[未]）。いずれも run 側の補題で、純粋 checker の健全性としては使えない。

### 5.12 S3s: ソース束 `SourceData` と `RootShowsAt` の設計（`docs/FG-CIRCUIT-PILOT.md` §67.3・§67.9。設計のみ、Lean に未記述）

reviewer 裁定2（ChildFn を結論の連言にする設計は可。ただし単なる含意は検索失敗で空虚）の反映:
- **被覆**: 全 call `k < 2` について `CallStmt`・`moduleByName` の接続を満たす `mc` の**存在**を結論に入れ、`b.body` の全 `inst` 文が某 `k < 2` に対応することも入れる。そのうえで `ChildFn mc …`。
- **この root の `instFields = []`**。一般の `SourceData` には、この制限を明示する（`instFields ≠ []` は被覆を証明していない。証明するか `CheckRoot` が false を返す）。
- **2 子の固定**: 範囲・順序（`K₀ = httpGetByte`、`K₁ = tlpCplByte`）・入力幅（`machineData.bsIn` から。freeze で値を固定）。`getD` の既定値（`fun _ => True`／`fun _ => 0`）には逃げない。
- **seed／初期値／reset = 0**: `SourceInputs`、`seed t st r = st r`（`r ∈ regs`）、`seed t st "rst" = 0`、`st0 r = f.init` を正確に述べ、**4 つを同時に満たす具体例を freeze に載せる**（前件が充足不能なら文は空虚）。
- **`SourceData.srcEq` に IR の正しさを入れない**。`srcEq` は元の `R` の値と `machineSource` の接続（`machine_source`、`machine_states`、`hftRootLink`）まで。`b`／`D` についての主張は `CheckRoot = true` からの結論に限る。

## 6. 比較と、最短経路の読み

(c1)/(c2) の欄は、**「全部品が揃って完成した後に期待する性質」と「現時点で欠けているもの」を分けて書く**（S3o の表は、未実装の checker・子の扱い・ソース接続・printer をすでに解いたように読めた。訂正）。

| 観点 | (a) 現行 | (b) 修正版 Corr | (c1) 完成後の見込み | (c2) 完成後の見込み |
|---|---|---|---|---|
| 未証明の文 | v11 の 9 binder（`Laws`、`CellPrem` ほか） | leaf 対応仮説の集合（置換）+ v12 再定式化 | 出荷物の突合（kernel の外の運用）と、「`(b₀, D₀)` がコンパイラの出力である」という運用上の結び（kernel 外） | 末尾の frame（checker が読む環境の対応） |
| 同じ元ソース・同じ artifact | 前提の下で yes | v12 が作れれば yes（未作成） | yes（固定した 1 出力の値） | yes（成功した各 run） |
| IP の維持 | 全て | 全て | 全て（コンパイラ不変） | 要確認（失敗時の throw か、既証明の未最適化 artifact への fallback かで変わる） |
| 台帳が減るか | いいえ | 供給されない限りいいえ（置換） | 局所成果として受理可。**FG 全体・全行減算にはしない**（reviewer 裁定） | 一般 checker + 接続が揃えば全称に近づく |
| 実 IO への残る対応 | `Laws`/`CellPrem` | 実 primitive ごとの対応（調査範囲で未供給） | 無し（文に `hr`・`L`・`CellPrem` が現れない） | 末尾のみ |

**現時点で欠けているもの（上の完成後の見込みは、これが揃って初めて成り立つ）**:

| 欠け | 内容 | 状態 |
|---|---|---|
| M1 checker（返された module を `MachineData` に照らして検査する純粋関数）と健全性 | 返された module を作る純粋関数は調査範囲で未発見（新実装は可能。§5.10 の 2）。鍵は validator の健全性。**未実装** | 行数見積り不能（§66.6 M1。比較の目安: 既存の run 側の健全性 3,153 行相当） |
| 子の `ChildFn`（M3）と連結（M4） | 既存の `machine_linked`/`machine_composed` は run 付き。run なしでの子の接続は**未実装** | 未見積り |
| ソース接続（§5.4 の環境対応） | `hftObCDT_T`・S2z の表検査は現在の成果（`env` の値についての文）。(c) で再利用するための `env` と kernel の定数 `R` の対応は**未解決** | 未見積り |
| printer・出荷物の同一性（M6・M7） | `toVerilogDesign`／`checkedOptimize` の出力（SV 文字列）と、IR の意味保存と SV の意味保存は別の義務（§67.4）。**未実装** | 未見積り |
| 採用入口（検査した同じ artifact だけを返す接続） | (c1) では不要（offline）、(c2) では必要。**未実装** | 未見積り |
| M5（最適化後の形） | S3q で測定済み（§5.11）: root の返却 module は raw。top は `refineCheck` の対象外（inst を含む）。 | 部分的に解決 |
| M8（FG の文面） | reviewer 裁定済み: 局所成果として受理、全体達成にはしない | 解決（裁定） |

**このパイロット（root 1 件、machine 経路）で FG に最短なのは (c) か**: S3o は「(c) の可能性が高い（未検証）」としたが、S3p で「純粋な組立関数が無い」ことが確定し、確度は弱まった（§6 末の S3p 再比較）。(a) と (b) は共に「実 IO の opaque primitive についての文」が調査範囲では未供給のまま残る（(b) は形を変えるだけで量化範囲も狭めない。§4.8）。(c) は run を経由せず返された値を検査する案で、**その成否は上の「欠けているもの」の M1 に集中する**。(b) の全面移植（案 1）は、reviewer 裁定により保留（今は開始しない）。

**(b) の費用の「2,500〜4,000 行」は、既知の部分（テンプレートがある部品: 追跡 ref の `get`/`set` の `Corr`、`pure`/`bind`、診断 leaf、同一 oracle の合成）の外挿であり、未知の部分（§4.7 の #1・#3・#4・#6・#9・#10 と v12 の再定式化）を含まない。**未知を含めた総量の見積りではない。

### S3p: 再比較（`docs/FG-CIRCUIT-PILOT.md` §66.8）

| 観点 | (a) 現行 | (b) 修正版 Corr | (c1) オフライン証明書 | (c2) コンパイラ内 checker |
|---|---|---|---|---|
| コンパイラの IO を仮定するか | `Laws`／`CellPrem` 全体 | leaf 対応仮説の集合 | **しない**（`hr`・`L`・`CellPrem`・`entry`・`closes` が文に現れない） | 末尾の frame のみ（範囲は未確認） |
| 調査範囲で未供給の前提が残るか | 残る（S3m で未供給） | 残る（opaque primitive ごとに未供給） | 構造上は文に現れない（ただし validator の成否に依存） | 残る可能性 |
| 同じ返された artifact | 前提の下で yes | v12 が作れれば yes | **値として yes**（閉じた項 `(b₀, D₀)` と出荷バイト列 `V₀`）。「compiler が返した値である」ことは kernel の外 | yes（成功した各 run） |
| FG の文面（`compile = ok` の全称）に合うか | yes | yes | **no**（artifact 固定の文。局所成果として受理可、FG 全体にはしない: reviewer 裁定） | ほぼ yes |
| 新規に要る最大の部品 | 調査範囲で未供給（`Laws`/`CellPrem`） | 2,500〜4,000 行（既知部分の外挿。未知を含まない） | validator（M1）＋最適化後の形（M5） | M1 ＋ 末尾 frame |
| 費用の確度 | 調査範囲で「供給の見込みが立たない」が高確度（不可能の証明ではない） | 低 | 低 | 低 |

**確度つきの読み**: (a) は最短でない（高。調査範囲で前提が未供給のため）。(b) と (c1) のどちらが短いかは決められない（低）。S3o の「(c) が唯一の案」は、既存の純粋な組立関数が調査範囲で見つからなかったため**弱まった**: (c1) の validator は translator の lowering の純粋な再記述で、既存の run 側の健全性（約 3,153 行相当）と同じ桁になり得る。(c1) の利点は、IO の対応仮説が文に現れず、既存の生成・連結・ソース側の部品が root で通り、artifact が小さい（top 256 文＋子 88／159 文）こと。(c1) の隠れた費用は M5（最適化後の module を validator が受け入れるか）と、FG の文面（M8）。推奨は出さない。次に小さい調査（実装なし）の候補は、M5・M1 の範囲・M8 の 3 点（§66.8）。

### S3s: ユーザーへの提示の範囲

この資料は (a)／(b)／(c) の比較であり、**(a)／(b) の TRUSTED 採用を今求めない**。(c) の最小実験（S3r、続いて M1 の小さい実証）は委任範囲で継続し、既知の費用を得てから、必要な保証変更・新 TRUSTED だけを具体的に判断に出す。E1 全面移植は保留、新 TRUSTED は未承認。

## 7. reviewer に確認したいこと（S3q の時点では、下の 1・4 は裁定済み）

**S3q 裁定の反映**: 4（(c1) を FG に数えるか）→ 局所成果として受理、現行 FG 全体の達成・全行減算にはしない。2・5（次の調査単位）→ M5・M1 の範囲は S3q で測定した（§5.11）。M8 は上の裁定で解決。以下は元の質問（記録）。
1. FG の定義が「`compileCircuit … = .ok artifact` の全称の定理」（戦略 §6）のままか、root 固定の artifact 証明書（(c1)）を FG の達成に数えるか。
2. (c) の調査（§5.4 の 1・2 のプローブ）を次の単位にしてよいか（実装を含まない）。
3. (b) を続ける場合、`Sig` の型付き other cell 化（§2 #1）で `ShippingHeapModel` の既存の文を保てると見てよいか。

4. **S3p 追加**: (c1)（artifact 固定の証明書。`compile = ok` の全称ではない）を FG の達成に数えるか。数えないなら (c1) は FG への経路ではなく、(c2) か (b) になる。
5. **S3p 追加**: 次の調査単位として、M5（root の `b₀` が `refineCheck`／`hierRefineCheck` の正規形に入るか）と M1 の範囲（256 文の `Operator`／`Stmt` の内訳と既存の演算の意味の補題の被覆）を測ってよいか（どちらも実装を含まない）。
