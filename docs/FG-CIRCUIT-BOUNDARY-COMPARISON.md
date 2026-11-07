# FG 回路パイロット: 境界の比較資料（案 2 の具体化）

Issue `sparkle-fg-circuit-pilot`、S3o。土台 `43a40e05`（S3n）。**未採用の比較資料。まず reviewer が確認し、その後にユーザーへ渡す。** 新 TRUSTED の採用・全面 E1 移植（案 1）の開始・v12 の作成はしていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

**【S3p 更新】** (c) の部分（§5.4・§6・§7）は S3p（`docs/FG-CIRCUIT-PILOT.md` §66、土台 `59a49445`）で更新した。更新箇所は「S3p」と明記した節と、各節末の「S3p 更新」の段落。S3o の本文は書き換えていない。S3p の結論は §6 末の「S3p: 再比較」。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

この資料の各数値と主張は、(i) 今回 kernel / Check55 で確かめたもの、(ii) リポジトリのファイルを読んだもの、(iii) 未検証（coder の見積り・推測）のどれかを明示する。(iii) を (i) の言葉で書かない。

## 0. 先に結論

1. **S3n の橋の `EnvCorr` は実 `getEnv` の成功 run と両立しなかった（kernel で反駁）。** 旧 `InitCorr`/`quietR` は**全 world で成立**し、実プロセスの quiet を何も制限していなかった。修正版 `RelE env`（環境を明示的な oracle `env` として run 全体で固定）は、その反駁に当たらず、モデル内（toy 意味論）で全仮説と成功 `getEnv` が同時に成り立つ。これは**モデル内の事実**で、実 pilot の証人ではない（`docs/FG-CIRCUIT-PILOT.md` §65）。
2. **修正しても (b) は「未証明の文を小さくした」とは言えない。** `RelE` は世界の量化範囲を狭めない（任意の `w` に対し、`w` から読み出した `h` が `RelE` で関係する。§3.2）。変わるのは文の中身（世界の等式 → 値の文）と、見える単位（leaf 操作）だけで、各 leaf の対応仮説は不透明な実 primitive についての**未供給の文**のまま残る。
3. **最短経路の暫定の読み（未検証）**: このパイロットの root `synth_hftPcieOutByte` は machine 経路（`machineShape?` = some、instance 2、slot 17、S1 §14.4 SNAPSHOT8b）にあり、(c) の「生成物を kernel で検査する」経路が、`Laws`/`CellPrem` の完成を要さない唯一の案である。ただし (c) が成り立つかの**主要な未確認が 4 つ**あり（§5.4）、それを小さい調査（実装でなく、既存の生成器が pilot root に適用できるかの確認）で先に潰すのが、(b) の全面移植より安い。推奨ではなく reviewer の判断材料である。
   **S3p 更新**: 主要な未確認 4 つは確定した（§5.10）。2（純粋な組立関数）の答えは**否**で、この項の「(c) が唯一の案」という暫定の読みは**弱まった**。(c) の IO を仮定しない形（(c1)）は成り立ち得るが、新規部品（返された module を検査する validator）が (b) と同じ桁になる可能性があり、(b) より安いとは言えない（§6 末）。

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
v11 の 10 binder が未供給: `L : Laws mref cref`（14 field）、`hquiet : L.O.quiet w`、`hsynth : sv w = some synthesizeChild`、`hcell : CellPrem MkRefd mref cref`（16 atomic）、`hD`、`hG`、`hT`、`hs`、`h0`、および `hr`（run の成功そのもの。これは前提であって未証明の文ではない）。S3m の調査では、`hcell` の第 1 field `ReadWorld sparkleChildCache`（`∀ w, getW r w = w`、**全 `w : Void IO.RealWorld`** 上）と `L.O.diag`（`StderrKeeps quiet`）が最初の阻害。これらを kernel で証明も反証もできない（opaque）ことは S3m で述べた。非空虚性（同時充足）は未確認で、矛盾も見つかっていない。

### 3.2 利用者への保証
「`pilotEntry3 hftRoot` の run が成功して `(b, D')` を返し、上の 10 前提が成り立つなら、その同じ `(b, D')` が元ソース `hftRoot` の意味を持つ（`RootArtifactMonoV`）」。**同じ元ソース・同じ返された artifact**（`hr` が結論の `b D'` を決める）で、IR の型検査ではない。ただし前提が実プロセスで成り立つことは**証明も検査もされていない**ため、利用者への無条件の保証ではない。

### 3.3 保つ IP
全て保つ（コンパイラ不変。出力の変更なし）。

### 3.4 残る台帳行
A.P-01、A.P-02（`hr` の検査で一部）、C.EN-4、`hD hG hT hs h0` の行。FG 75 / T1 57 のまま（減らない）。

### 3.5 操作の種類と量化範囲
`Laws.O.diag` は全許容文脈・全 `Diag p`（任意 `Handle`）・全 quiet world。`CellPrem` は全 world。全 `Expr`、全 `Meta.Context`（`frame`）。

### 3.6 費用
追加費用 0。ただし (a) のままでは前提の充足可能性を示す道がない（S3m）。

## 4. 案 (b): 修正版 Corr（明示状態・oracle 固定）の保証と、実 IO に残る対応

### 4.1 今回の修正（kernel 済。`Tools/ShippingFGCircuitS3oFix.lean`）
- 反駁: `envCorr_inconsistent`（旧 `EnvCorr k` + 実 `getEnv k` の 1 つの成功 run で `False`。`hEmpty`（env = `[]`）と `hSome`（env = `[(k,"v")]`）が同じ `w` に旧 `Rel` で関係し、同じ実戻り値 `a` が `none` と `some "v"` の両方に等しくなる）。実 run は任意の world から必ず存在する（`runsTo_getEnv`、`BaseIO`）。
- 反駁: `oldInit_any_world`（旧 `InitCorr w ∧ quietR w` が任意の `w` で成立）、`oldQuietR_eq_true`（`quietR = fun _ => True`）。
- 修正: `RelE env h w := cv w = h.cache ∧ sv w = h.synth ∧ dv w = h.depth ∧ h.reg.env = env`。`CorrE env`、`GetCorrE`/`SetCorrE`/`StderrCorrE`/`EnvCorrE env k` を oracle `env` に対して再記述。oracle は `corrE_bind` の仮説・継続の仮説・結論のすべてで**同じパラメータ**で、leaf ごとに選び直せない。`corrE_bind`、`bridge_smallE`、`real_small_consequenceE` を再証明。同一 oracle の 2 回読み `bridge_env_twice`/`real_env_twice`（両方の読みが `lookupEnv env k`）。
- 対照: 旧 shape が許した「環境の異なる 2 状態が同じ world に関係する」ことは `relE_not_both`（同じ oracle では不可）で拒否。oracle が `k` 未設定なら実の観測 `some v` は不可（`envCorrE_observation_committed`）。
- 同時充足（**モデル内**）: toy 意味論で、1 つの oracle・1 つの開始 world・quiet なモデル heap・全 leaf の対応・合成プログラムの対応・成功 `getEnv "HOME"`（`some "/root"`）が同時に成立（`Toy.simultaneous_sat`）。

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
「oracle `env` と上の leaf 対応が実プロセスで成り立つなら、`pilotEntry3 hftRoot` の成功 run が返す `(b, D')` は元ソースの意味を持つ」。**同じ元ソース・同じ返された artifact**（v12 の結論が v11 と同じ `(b, D')` を対象にする場合）。ただし v12 は未作成。(a) との違いは仮説の形（世界の等式 → 値の文）と局在（leaf 操作ごと）で、**仮説が供給されないことは (a) と同じ**。

### 4.5 保つ IP
全て保つ（コンパイラ不変）。

### 4.6 残る台帳行
A.P-01、C.EN-4 は、leaf 対応仮説の集合に**置き換わる**だけで、供給されない限り減らない。置換後の行数は、操作の種類（§2 の 10 行）に比例し、現時点では**数えていない**（FG 75 は不変）。新 TRUSTED の候補になる（採用していない）。

### 4.7 費用
- coder の見積り（**未検証**）: 全体で 2,500〜4,000 行（S3n 小接続 約 300 行を、`SideRef` 24、`Diag` 残り 8、Meta primitive 十数個、telescope 4、例外、`mkRef`、`modify` へ、leaf あたり 30〜60 行で拡張）。
- 既知の部分（テンプレートが今回までにある）: 追跡 ref の `get`/`set` の `Corr`（`getCorrE_of_readWorld`、`setCorrE_depth`）、`pure`・`bind`（`corrE_pure`/`corrE_bind`、型 ~20 行）、診断 leaf（`getStderr`/`getEnv`/`eprintln` の model 側の保存補題）、同一 oracle の合成。今回の実測: 修正（反駁・`RelE`・bridge・toy・同時充足）で `Tools/ShippingFGCircuitS3oFix.lean` 433 行（反駁と toy を含む）、Check55 195 行。
- 未知の部分（テンプレートがなく、行数を見積れない）: §2 の #1（`Sig` の型付き other cell 化と `ShippingHeapModel` の既存文の保持）、#3（fresh ref の単射対応と相異なる ref の存在）、#4（失敗側の対応）、#6（高階の telescope）、#9（`for`・`partial`・相互再帰の測度）、#10（`pilotEntry3` の run 全体の分解）、v12 の再定式化が成り立つか。**2,500〜4,000 行は既知部分の外挿であり、未知部分を含まない**。

## 5. 案 (c): 元ソースの意味と**返された IR** の対応を kernel で検査する証明・証明書（調査のみ）

コンパイラの IO 全体を正しいと仮定せず、**返された artifact という値**が元ソースの意味と一致することを、kernel で検査する。戦略 §5 の「既存生成器が証拠を出し、小さい純粋 checker で検査」に当たる。**新規の全面実装はしない。以下は候補調査で、成立は未確認。**

### 5.1 リポジトリに既にあるもの（ファイルを読んで確認）
- **`#machine_endpoint f`**（`Tools/ShippingMachineCommand.lean`）と `machine_trace_of_data`（`Tools/ShippingMachineAuto.lean`）: 元の宣言 `f` の本体を `MachineData` に読み、`MachineData.ok`（全 side condition の 1 つの Bool）と 5 つの等式を `Eq.refl` で kernel 検査して `f.machine_sound : MachineTrace …` を生成する。コーパス 120 宣言で生成済み（`docs/ShippingCompiler-Coverage.md`）。**元ソース側の kernel 検査は既にある。** `unq` は意図的に未検証で、等式の kernel 検査が受理の根拠。
- **ただし生成される `f.machine_sound` の前提は run**: `synthesizeCombinationalCore_machine_sound` は `hr : RunsTo (synthesizeCombinationalCore declName [] false) … (m, d) w'` と `MachineDefines`・`MachineCloses`（run がこの shape を読んだ／`let` を結んだ）を取る（`Tools/ShippingMachineEntry.lean:2388`）。FG の証明では `MachineDefines` を `Laws`・`hquiet`・`GetEnvFrame` から供給する（`machineDefinesLinked_of_env`、`Tools/ShippingFGCircuitLinked.lean`）。つまり**現行の machine 経路の端点は IO run を経由し、(c) の「IO を仮定しない」形ではない。**
- **返された module に対する純粋な decidable 検査と kernel 済の健全性**: `refineCheck`（`Sparkle/IR/RefineCheck.lean`）+ `refineCheck_transfer`（`Tools/ShippingRefineSoundness.lean`）、`EmitSem.seqCheck`（出力 Verilog の検査）、`machine_ships`/`machine_ships_wired`（`Tools/ShippingMachineShipping.lean`）。コーパスでは 113 の machine 経路宣言のうち 107 で全 gate が成立し 6 が `seqCheck` で棄却（`docs/ShippingCompiler-Coverage.md`）。コンパイラ自身も `mergeChecked`/`checkedOptimize` で `refineCheck` を呼び、棄却時は未 merge／未最適化の module を返す（検査失敗を throw にはしない）。
- `machineShape?` は純粋関数（同文書）。

### 5.2 pilot root の証明書に含まれるもの（案）
1. **返された artifact そのもの**: `pilotEntry3 hftRoot` が返す `(b, D')` を 1 回のコンパイル実行からシリアライズした**閉じた Lean 項** `(b₀, D₀)`（top と子 module `httpGetByte`・`tlpCplByte`）。
2. **元ソースの端点**: `synth_hftPcieOutByte`（公開版 `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte`、private な元定義ではない）の `MachineData` と `MachineData.ok`、5 つの等式（`rfl`）。
3. **artifact とソースの接続**: `MachineTrace data b₀ D₀` に相当する kernel 検査可能な命題。**これを `hr` なしで得る方法は既存にない**（既存の `machine_trace_of_data` の結論は「run が返した module」について）。必要なのは、module を `data` から組み立てる純粋関数（または module と `data` の対応を判定する純粋 checker）と、その健全性定理。
4. **出荷物の同一性**: 出荷される Verilog が `emit D₀` と一致することの検査（`emit` は純粋）。
5. **子 module の接続**: `D₀` の各 module が自分の宣言に対して検査され、instance の参照先が `D₀` に存在し名前が一意であること（Design の整合）。

### 5.3 同じ artifact を固定するか
固定する。ただし条件付き: 証明書は**記録した 1 回の出力**について成り立つ。コンパイラの変更（配線番号付け、`machCanonAp` のような名前の正規化。実際に `fsmHoldCdo` の配線番号が 1 つ変わった例が `Coverage.md` にある）で出力が変われば**再生成が要る**。「全ソースについてコンパイラが正しい」という一般定理ではなく、「このソースとこのバイト列」という artifact 固定の保証になる。IR の型検査ではなく、**観測（trace）の一致**を言う。

### 5.4 主要な未確認（(c) が成り立つかを決める 4 点）
1. **pilot root に `#machine_endpoint` が適用できるか**: docs §14.4 の未確認項目 5（`insts` 付き shape で `dataOfAt` が正しいデータを返すか、`synth_hftPcieOutByte` に `machine_*` が生成されるか）が**未確認のまま**。`machine_*` が既に生成されている宣言は instance を持たない場合が多い可能性がある（調べていない）。
2. **module を `data` から組み立てる純粋関数があるか**: 既存の `machine_trace_of_data` は run を経由して「module = 組立の結果」を使っている可能性が高い（`MachinePreserves`、`synthesizeCombinationalCore_reads`）。純粋な組立関数が独立に存在するか、IO の `synthesizeMachineCertified` の中だけにあるかは**未確認**。後者なら、(c) は新しい組立関数の再実装と、コンパイラ内の同等性の証明を要し、「新規全面実装は不要」の範囲を超える。
3. **子 instance（`httpGetByte`・`tlpCplByte`）の扱い**: 親の module は子を名前で参照し、子の合成は `synthesizeChild`（`sparkleChildCache` を含む IO）を通る。証明書では子も閉じた module として検査して名前で結ぶので `CellPrem`/`Laws` は要らないはずだが、子の module が**親の run と同じ**出力であること（名前・配線の一致）の検査を含める必要があり、既存の `EndpointLink`（S1k）との関係は**未確認**。
4. **ソース側の `CD`/`CDX`**: `HftObCD`（`CD [] hftRootValue (MonoTy shHft) synth_hftPcieOutByte`）は `CD` に規則がなく（利用者定義定数と構造体射影）、新関係 `CDX` を足した段階で、導出の供給は未完了（`docs/FG-CIRCUIT-PILOT.md` の `hcd` の節）。(c) の「元ソースの意味」はこの `SourceDenotesMono` と同じ義務を負う。

### 5.5 コンパイラの IO を仮定しないか
2 つの形があり、残る信頼が異なる:
- **(c1) オフラインの証明書**: 出力を Lean ファイルに書き出し、kernel が検査する。コンパイラの IO は**どこにも仮定されない**。残るのは「出荷物 = `emit D₀`」の突合（バイト比較またはハッシュ。kernel 内で `decide` するか、外部ツールかは**未決**）と、`D₀` を作った実行が出荷と同じ入力で行われたこと（運用手順）。保証は artifact 固定。
- **(c2) コンパイラ内の checker**: コンパイラが成功を返す前に純粋 checker を呼び、失敗なら throw する（戦略 §3.4）。checker の健全性は kernel 検査。残るのは「成功 run の末尾で checker が artifact に対して true だった」という **run の末尾の構造**の証明（`RunsTo.bind` の分解と checker の純粋性）で、`Laws`/`CellPrem` 全体は要らない見込み。ただし checker が読むソース環境が run 開始時の `envAt cref w` と一致する（env が run 中に宣言 `X` について変わらない）ことの frame が要り、**これが `Laws` 相当の frame を再び要求しないかは未確認**。

### 5.6 保つ IP
(c1) はコンパイラ不変なので全て保つ（出力変更なし）。(c2) は検査失敗を throw にするので、**以前成功した入力がエラーになり得る**（戦略 §5 の指摘）。現在のコンパイラは検査失敗時に fallback するため（`mergeChecked`）、throw に変えると必要 IP が落ちないかをコーパス（107/113）で再確認する必要がある。

### 5.7 残る台帳行
(c1): pilot root 1 件については A.P-01・C.EN-4 の行を通らない（run を使わない）。ただし FG の定義が「`compileCircuit … = .ok artifact` の全称の定理」（戦略 §6）なら、artifact 固定の証明書はその形の定理ではない。FG の行を減らすと数えられるかは、**reviewer の判断**（本資料は数を変えない）。(c2): A.P-02 の一部と、末尾の frame の行。減る数は未見積り。

### 5.8 操作の種類と量化範囲
(c1): 量化は閉じた artifact 1 つと、`MachineData` の有限データ。全 world・全 run の量化は無い。(c2): checker の健全性は全入力で kernel 検査し、run 側は末尾の bind 分解のみ。

### 5.9 費用
既知: `#machine_endpoint` の 1 宣言あたりの kernel 検査は 0.1〜1.5 秒（`Coverage.md` の 55 宣言での測定）。`refineCheck` の吸収は既存。**未知（行数を見積れない）**: §5.4 の 4 点、シリアライズ（閉じた Lean 項への書き出し。巨大 module の kernel 検査の規模。CRC の正規形は 0.5〜0.75M ノード）、`emit` 突合の方式。調査自体（実装なし）の作業量: §5.4 の 1 と 2 を `kjob lake env lean` のプローブで確認する程度で、小さい。


### 5.10 S3p: §5.4 の未確認 4 点の確定（`docs/FG-CIRCUIT-PILOT.md` §66。読みとプローブ。実装なし）

出所の種類: **[読]** ファイルを読んだ、**[プローブ]** scratch での読み取り専用実行（1 環境・この base の値）、**[未]** 未確認。

1. **pilot root に `#machine_endpoint` は適用できるか — できる（S1k で適用済み）。** root には `machineData`・`machine_ok`・`machine_body`・`machine_sound`・`machine_states` 等 21 個の定数がある。**無い**ものは `machine_closes`・`machine_ships*`・`machine_composedT*`・`machine_ships_hier`。理由: `machine_ships*` は `Tools/ShippingMachineCommand.lean:2728` の `if r.shape.insts.isEmpty`（insts 付きは設計上出さない）、`machine_closes` はデータに呼び出しがあると作れない（`Tools/ShippingMachineClosesGen.lean:119` のエラー）、`machine_composedT*`／`machine_ships_hier` は `endpointParts`（`Tools/ShippingMachineSeqCommand.lean:71`）が root の頭 `machine_trace_of_tele_ext` を持たない（`no wired twin for its head`）。**`#machine_linked` と `#machine_composed` は root に通る**（[プローブ]）。ただし生成される `machine_sound`／`machine_linked`／`machine_composed` は全て `hr`・`entry : MachineDefines`・`closes : MachineCloses` を取る（run の 11 binder）。
2. **Module（と Design）を組む純粋関数はあるか — ない。** 純粋なのは仕上げの `closeLets`／`closeMachine`／`closeInstsG` と後処理（`dropZeroWidthModule`／`mergeChecked`／`checkedOptimize`／`toVerilogDesign`）だけ。中核は `synthesizeMixedCertified`（`MetaM`、fresh な id と `IO.Ref` のキャッシュ）＋ translator（`CompilerM`、グローバル `IO.Ref`）。既存の健全性の文は `∃ ids cache, … MachineWired …` の存在形で、`m = build …` の等式ではない。→ `pureBuild src = M` は書けない。
3. **子 instance の接続 — 覆うが run の仮定は外れない。** `machine_linked`（子は `ChildFn mc …` を仮定）、`machine_composed`（子は `MachineRun child shape mc`＝子の run の存在を仮定）はどちらも root の 2 つの子を扱うが、`hr`・`entry`・`closes` が要る。FG 側の鎖（`machine_ships_hierC_runOff`、`machine_linked_callsServed1` 等）も `L`・`hr`・`CellPrem` 由来の前提を取る。
4. **ソース側 — `CDT`（`cdvT`）が root で使え、導出は閉じている。** 「ソースの意味 = 返された IR の意味」を述べる既存定理は v11 `HftFinalStmtOffCombined11`（前提 10 binder: `L hquiet hsynth hr hcell hD hG hT hs h0`）。ソース側（`SourceDenotesMonoV`、`ObservationsEqualMono`）は環境 `envAt cref w` にだけ依存し、artifact 側（`HasConcretePackage`）が `hr` を要する。run なしの閉じた source 側の部品として `machine_states`・`machine_source`・`hftRootLink` がある（定数 `synth_hftPcieOutByte` そのものについての文）。

**この確定が (c) について意味すること**: 「`#machine_endpoint` が通るか」「接続の文があるか」という 1・3・4 は肯定的だが、いずれも run 経由。(c) を IO 非依存にする鍵は 2 で、答えは否。したがって (c1)（オフライン証明書）の新規部品は、返された module を `MachineData` に照らして検査する純粋 checker（validator）とその健全性になる（§66.6 の M1〜M8）。

## 6. 比較と、最短経路の読み

| 観点 | (a) 現行 | (b) 修正版 Corr | (c) 証明書／checker |
|---|---|---|---|
| 未証明の文 | v11 の 9 binder（`Laws`、`CellPrem` ほか） | leaf 対応仮説の集合（置換）+ v12 再定式化 | (c1) 出荷物の突合のみ／(c2) 末尾 frame |
| 同じ元ソース・同じ artifact | 前提の下で yes | v12 が作れれば yes（未作成） | (c1) yes（固定した 1 出力）、(c2) yes（成功した各 run） |
| IP の維持 | 全て | 全て | (c1) 全て／(c2) 要確認 |
| 台帳が減るか | いいえ | 供給されない限りいいえ（置換） | pilot については可能性あり（FG の定義次第） |
| 実 IO への残る対応 | `Laws`/`CellPrem` | 実 primitive ごとの対応（供給不能） | (c1) 無し／(c2) 末尾のみ |
| 費用の未知 | 非空虚性が示せない | §4.7 の未知（型付き cell、fresh ref、高階、測度） | §5.4 の 4 点 |

**このパイロット（root 1 件、machine 経路）で FG に最短なのは (c) の可能性が高い（未検証）。** 理由は、(a) と (b) が共に「実 IO の opaque primitive についての未供給の文」を最後まで残す（(b) は形を変えるだけで量化範囲も狭めない）のに対し、(c) は run を経由せず返された値を検査する唯一の案だから。ただし (c) の成否は §5.4 の未確認 4 点（特に 2: 純粋な組立関数の有無）で決まり、2 が否なら (c) は新規実装になり、(b) より安いとは言えなくなる。**(b) の全面移植（案 1）は、(c) の調査結果が出るまで開始しない**のが、現在の読みである（reviewer が既に案 1 を今は開始しないと裁定済み）。

### S3p: 再比較（`docs/FG-CIRCUIT-PILOT.md` §66.8）

| 観点 | (a) 現行 | (b) 修正版 Corr | (c1) オフライン証明書 | (c2) コンパイラ内 checker |
|---|---|---|---|---|
| コンパイラの IO を仮定するか | `Laws`／`CellPrem` 全体 | leaf 対応仮説の集合 | **しない**（`hr`・`L`・`CellPrem`・`entry`・`closes` が文に現れない） | 末尾の frame のみ（範囲は未確認） |
| 供給できない前提が残るか | 残る（S3m） | 残る（opaque primitive ごと） | 構造上は残らない（ただし validator の成否に依存） | 残る可能性 |
| 同じ返された artifact | 前提の下で yes | v12 が作れれば yes | **値として yes**（閉じた項 `(b₀, D₀)` と出荷バイト列 `V₀`）。「compiler が返した値である」ことは kernel の外 | yes（成功した各 run） |
| FG の文面（`compile = ok` の全称）に合うか | yes | yes | **no**（artifact 固定の文。reviewer の判断） | ほぼ yes |
| 新規に要る最大の部品 | 供給不能 | 2,500〜4,000 行（既知部分の外挿。未知を含まない） | validator（M1）＋最適化後の形（M5） | M1 ＋ 末尾 frame |
| 費用の確度 | 「完成しない」が高確度 | 低 | 低 | 低 |

**確度つきの読み**: (a) は最短でない（高）。(b) と (c1) のどちらが短いかは決められない（低）。S3o の「(c) が唯一の案」は、純粋な組立関数が無かったため**弱まった**: (c1) の validator は translator の lowering の純粋な再記述で、既存の run 側の健全性（約 3,153 行相当）と同じ桁になり得る。(c1) の利点は、IO の対応仮説が文に現れず、既存の生成・連結・ソース側の部品が root で通り、artifact が小さい（top 256 文＋子 88／159 文）こと。(c1) の隠れた費用は M5（最適化後の module を validator が受け入れるか）と、FG の文面（M8）。推奨は出さない。次に小さい調査（実装なし）の候補は、M5・M1 の範囲・M8 の 3 点（§66.8）。

## 7. reviewer に確認したいこと
1. FG の定義が「`compileCircuit … = .ok artifact` の全称の定理」（戦略 §6）のままか、root 固定の artifact 証明書（(c1)）を FG の達成に数えるか。
2. (c) の調査（§5.4 の 1・2 のプローブ）を次の単位にしてよいか（実装を含まない）。
3. (b) を続ける場合、`Sig` の型付き other cell 化（§2 #1）で `ShippingHeapModel` の既存の文を保てると見てよいか。

4. **S3p 追加**: (c1)（artifact 固定の証明書。`compile = ok` の全称ではない）を FG の達成に数えるか。数えないなら (c1) は FG への経路ではなく、(c2) か (b) になる。
5. **S3p 追加**: 次の調査単位として、M5（root の `b₀` が `refineCheck`／`hierRefineCheck` の正規形に入るか）と M1 の範囲（256 文の `Operator`／`Stmt` の内訳と既存の演算の意味の補題の被覆）を測ってよいか（どちらも実装を含まない）。
