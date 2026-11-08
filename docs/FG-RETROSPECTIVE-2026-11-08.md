# FG 従来方式の区切りと失敗事例（2026-11-08）

## 判断と記録の範囲

ユーザーの指示により、従来の FG 全面証明の到達点を保存し、開発の主軸を `#verify_elab_deep` の拡張へ移す。FG を完成扱いにせず、未解決前提を TRUSTED に移して完了にも数えない。受入済み台帳は **FG 75 / T1 57**。

本書は reviewer が受け取った提出・裁定のまとめであり、全 SHA を今回再ビルドした報告ではない。下記 SHA、定理名、Check は再検証の入口として残す。ローカル `par/fgc-s1` は最新提出を含まないため、ブランチ名だけで最新版を指したと解釈しない。coder は各事例に現存する commit・Job・ログへの参照を補完すること。

二つの試行を区別する。

1. 実コンパイラの run から、前提を供給して FG を組み立てる方式。
2. その境界を避けるための、回路意味 carrier・検査付き入口・新しい validator の試行。

後者も個別 root の確認から一般定理への接続が未完であり、従来方式の完了でも失敗の証明でもない。

## 何が進んだか

ユーザーの把握では約2週間で FG は100前後から75まで減った。既存定理による導出、不要な binder の除去、計上の統合が含まれる。これらを全部同じ重さの証明進捗とは数えないが、実質的な前提除去の実績はある。残り75行すべてが解けないと分かったわけではない。

pilot では source の導出、子呼び出しとの意味一致、同じ返却 artifact への接続、環境や reader の有限検査、開始 cache 前提の除去等が進んだ。v11 はなお `L hquiet hsynth hr hcell hD hG hT hs h0` を持つ。`hr` は成功実行の前件で、他と同じ未証明法則ではない。

新 validator 側では、一般の `checkComb_sound` と `ofData_sound`、閉じた子 `httpGetByte` の `k0_childFn` が得られた（615b4b90、Check57/58v、m3uv-1cf9）。（coder 訂正: `checkComb_sound` と Check57 は S3t（6a59d36e、7da493ad、§69）、`ofData_sound`・`k0_childFn`・Check58v は S3v（§71）。S3u は freeze 境界だけ（§70）。615b4b90 は S3u+S3v の merge の上の docstring 修正で、m3uv-1cf9 はその SHA の検証。）その後 S3y/S3y2（8cf6beef、Check60、m3y2-794b）で一般 G1 `checkData_sound` と G2 `certifiedEntryC_sound` を得たが、中間意味（MachineData）までで、元宣言との接続（DeclDenotes）は未供給。root 全体、元宣言から一般的な入口への橋、FG の最終消費側は未完。個別成果から FG の行を減らしていない。

## 失敗事例と原因

### 1. CV の全称束縛が結論を壊す

- 症状：任意の `CV : ConstValueRel` に対して関数性を結論に要求。常に True の関係では成立しない。
- 根拠：40b176fe、CVTopCheck の `cvTop_not_functional` / `fgG_refutes_outer`。
- 分類：反例による仕様欠陥。証明工数の問題ではない。
- 対応：具体的な意味 carrier を検討。さらに任意 PT では、行の型付けだけでソースの意味の存在を保証できないことが露呈した（bc4e180f、PTlit と Signal root）。（coder 補足: PTlit での反駁は条件付き。PTlit では文が偽または空虚になるが、入口仮説が充足可能かは調べていない。Signal root の停止事実は meta 評価によるもので、kernel の定理ではない。）
- 教訓：関数性、型の健全性、対象宣言の意味の存在は別の義務。文を固定する前に、全称引数の極端な例と非空虚な成立例を試す。

### 2. 実行 world と環境を結んだつもりで結んでいない

- 症状：途中 world の値を固定しても、その world が対象 run の連鎖の途中だとは言えなかった。全 world の静的環境条件も実 ref モデルに合わなかった。
- 根拠：S1d の `not_staticEnv`、S1f→S1g の MachineDefinesRun→MachineDefinesLinked、74d5ca1d。
- 分類：仮説の適用範囲・run 接続の欠陥。
- 対応：prefix/body/suffix と読み取り位置を同じ run に結合。別 world、切断した連鎖の負対照を追加。
- 教訓：同じ型・同じ値の記述だけでは、同じ実行・同じ artifact の証明にならない。

### 3. opaque IO 境界で現実の成立例を供給できない

- 症状：CellPrem の最初の ReadWorld、Laws の診断保存則から供給が止まった。
- 根拠：S3m cb923479、Check53。`ST.Prim.Ref.get`、`IO.getStderr` 等について必要な kernel 等式/API が調査範囲内で得られなかった。
- 分類：既存モデルと実装の対応が未証明。矛盾や証明不能性の証明ではない。
- 注意：実環境で ref 値が変わらない観測は、全 world の等式や Laws と CellPrem の同時充足を証明しない。quiet=False の Laws も実用的な成立例ではない。
- 教訓：長い条件付きの組立より先に、主要法則が同時に成り立つ非空虚なモデルと実行との橋を確かめる。

### 4. 明示状態モデルへの移行も対応境界を消さなかった

- 症状：小さいモデルでは法則が証明できたが、実 IO への Corr は未供給のまま。さらに旧 EnvCorr は矛盾、旧 quietR は恒真だった。
- 根拠：S3n 43a40e05、S3o 59a49445、Check54/55。`envCorr_inconsistent`、`oldQuietR_eq_true`。（coder 補足: 2 つの反駁定理は S3o（Tools/ShippingFGCircuitS3oFix.lean:55、:65、Check55）にあり、S3n ではない。）
- 原因：旧 Rel が環境を拘束せず、同じ real world に異なる環境を対応させ、getEnv の同じ返り値へ異なる値を要求した。
- 対応：oracle を固定した RelE/CorrE。toy の同時充足例は得たが実 runtime の対応証明ではない。
- 教訓：小さいモデルの整合性と実装への適合性は別。全面移植の2,500–4,000行は見積りに過ぎず、未知の部分と対応証明は別途残る。全面移植は保留。

### 5. 構文代入・値の表現が対象回路を覆わない

- 症状：一般代入補題が現規則では成立しない場合、Type 0 の Dyn に再帰子・motive・型クラス引数が入らない場合があった。
- 根拠：d1e60233 の代入負対照、bc4e180f の PTcorpus、404e597a の carrier 比較。（coder 訂正: d1e60233 自身は一般代入補題が「偽になりうる」と書いていて、具体的な反例は作っていない。kernel が示したのは `substS` が `betaS`／`instForallS` と可換でないことだけなので、分類は「未供給（反例候補あり）」。引用した 5 コミット（d1e60233、bc4e180f、404e597a、6fd58e9e、e37da005）はどれも `CONSTVALUEE_FREEZE_DRAFT.md` だけの変更で、404e597a は比較表の数値 2 行の修正であって比較そのものではない。）
- 対応：valuation 経由の app/let、狭い回路 primitive 規則、静的 List.rec。Signal の展開停止だけでは全コーパスの再帰子は消えなかった（6fd58e9e、e37da005）。
- 教訓：任意 Lean を意味モデルに取り込む費用と、有限な回路記述を扱う費用を分ける。停止集合を広げても、その primitive の意味の正当化は必要。

### 6. 証明項の共有破壊と誤った性能測定

- 症状：中間 Expr を木として複製し、28GB で bad_alloc。非同期の宣言登録時間を kernel 検査時間として報告した例もあった。
- 根拠：S2b 5dc8972f、S2q 64742f1a、S2t/u 9503bb49。S3a2 の internE も DAG を木として歩いていた。（coder 訂正: 28GB の bad_alloc が最初に記録されたのは S1w2（9e6556e9、§23.6）で、S2b（5dc8972f、§30.3）は比較と修正。internE の木の歩きは S3a（d64e65af、20 分を超えた build）で起き、S3a2（6a871de2）がメモ化による修正。）
- 対応：共有を保つ置換・閉包環境・メモ化。同期 addDeclCore で測り直し。root の導出は条件付きで kernel 約6.9秒まで到達した（特定環境・1回の値であり一般的な時間保証ではない）。
- 教訓：停止をすぐ証明方式の限界と解釈しない。DAG/tree、elaboration/kernel、同期/非同期、ピークメモリを区別する。

### 7. 検査器・生成器にもバグがあった

- 症状：引用 cache の α 同値が束縛名を取り違え、生成器が instance を見ずに枝を選択。署名比較器は証明らしい名前やローカル BEq instance に依存していた。
- 根拠：S2q/u、S2w 6aaec627、S2x 0afddb92、S2v merge 修正6a331dc5。
- 対応：厳密な Expr 一致、実際の instance の確認、Prop 型の確認、固定標準 instance、正負の同じ正規化、kernel の拒否対照。
- 教訓：mutant の数は検査器の正しさを保証しない。生成器は非信頼、完成証明は kernel が検査する設計を守る。署名検査は意味保存の代用ではない。

### 8. artifact の観測を意味保存の橋と取り違えかけた

- 症状：閉じた最適化候補 S0 と実 optimizer の出力の一致は観測だけ。partial な optimizer や String 操作は kernel 評価できず、compiled check=true と kernel 証明が分かれた。
- 根拠：S3r b8fbe491、Check56。階層 top は17レジスタを持ち、assign/inst のみの既存 SV 移送補題はそのまま使えない。（coder 訂正: 17 レジスタと assign/inst だけの補題 `combStmtI` の所見は §67.9（S3q、S3s 8bb4efd4）にあり、S3r の §68 ではない。b8fbe491 の merge にはそれも含まれる。）
- 対応：返却 IR、検証した最適化候補、印字された SV を区別。観測を定理として数えない。
- 教訓：検証したものだけを返す構造と、その後にある変換の保証を明示する。

### 9. 局所成果の積み上げが一般 FG の完成に結び付かなかった

- 症状：多数の Check・root 固定定理・binder の置換が増えたが FG75/T157は減らなかった。
- 原因：同じ境界の細分化・言い換えが多く、元宣言から一般入口と FG 最終結論までの接続を後回しにした。既存 DeepElab との重複比較も遅れた。
- 責任と改善：reviewer は局所受理と目標の進捗を分けて報告すべきだった。coder と reviewer の双方で、作業単位ごとに最終結論へ何を渡すかを先に固定する。
- 注意：台帳の不変は成果ゼロを意味しないが、一般 FG の完成を意味しないことも同時に示す。

## 保存・再利用と再開条件

既存の run 証明、source carrier の関数性、同一 run/artifact の接続補題、一般 comb validator、入力境界と階層の検査、反例と負対照、IP baseline を保存する。新しい方法に都合よく過去の失敗を削除しない。

従来 FG を再開する条件は、残り75行のうち実際に除去可能な候補、実 runtime 境界の扱い、最終文への接続を具体化できること。全行を opaque IO の問題に一括分類しない。再開時は承認済み SHA と未受理成果を区別する。

## 次の主軸：verify_elab_deep の拡張

既存 `Tools/DeepElab.lean` には Cdo/CdoM/CdoW.elab_general と、元 Signal・実生成 IR への個別の橋がある。確認したコマンド実装には single-module 制限がある。一般深層言語の定理は、shipping compiler 全体の健全性定理そのものではない。

目標を二つに分ける。

1. 成功して返す artifact のすべてを検証し、検証した同じ artifact だけを返す。未検証の fallback は通さない。
2. 必要IPの固定一覧がすべてコンパイル・検証に成功する。構文・状態・階層・メモリ・複数出力の不足と性能を一覧化する。

元ソース→返却IR→最適化→SVの保証範囲と信頼基盤は段階ごとに明記する。既存方式の axioms/decision procedure の実際の依存も監査する。従来 FG の行をこの対応率に読み替えて減らさない。

進行中 S3w/S3y は commit・検証結果・未完箇所を保存し、新しい大規模拡張へ自動的に進まない。利用可能な一般補題は再利用候補とする。次の実装は DeepElab の対応不足と再利用比較を踏まえて選ぶ。

## 引き継ぎ時に補う記録

- 各事例の該当 commit/ファイル/定理、再現コマンド、成功・失敗 Job とログ所在。
- kernel 反駁／未供給／観測／未測定を明示した結果。
- 進行中 Job の最終 SHA・dirty・検証結果・残件。終了と完成を混同しない。
- FG 約100→75の内訳（証明による除去、不要前提の除去、重複計上修正）を既存台帳から集計する。推測で比率を書かない。→ 付録 B。記録上の開始値は「約100」ではなく 146 ブロック（段 1 の重複整理で 110）。

記録上の障害：本書作成時、managerctl は completed pod（Failed）への exec エラーで利用できず、Issue の更新は未実施。復旧後にこの文書と方針転換を登録する。

## 付録 A: 根拠の照合（coder、2026-11-08）

ファイル・git の履歴・記録済みの kjob ログを読んだだけで、何も再ビルドしていない。各 Check の結果は記録済み Job のログ（exit code と FGCIRCUIT.. 行）からの引用。


対象: `docs/FG-RETROSPECTIVE-2026-11-08.md`（par/fgc-retro 241a05d2）。
方法: 読み取りだけで行った（`git cat-file` / `git log` / `git show` / `git grep` / `git branch -a --contains`、`docs/FG-CIRCUIT-PILOT.md`（origin/par/fgc-s1 8cf6beef、4210 行）、`~/git/.kjob-state/namespaces/sparkle-dev/<job>/{meta.json,builds/*.json,output.log,commits.json}`、coder の transcript）。今回はビルドしていない。下の「Check」欄の結果は、記録に残る Job の exit code と output.log の行であり、今回の再実行の結果ではない。

共通事項:
- 引用された SHA 19 個（8cf6beef を含む）はすべて commit として存在する。
- ローカルの `par/fgc-s1` は a4c6e62d（S1h §13）にあり、origin/par/fgc-s1 より 509 commit 遅れている。本書 7 行目の注意は正しい。
- d4 系（40b176fe, bc4e180f, d1e60233, 404e597a, 6fd58e9e, e37da005）は origin/par/fgc-s1 には含まれない。par/cvtop・par/d4*（と origin の同名ブランチ）に含まれる。経路の違う系列なので矛盾ではない。
- 再現コマンドの形はどれも同じ: その SHA の worktree で `kjob -N sparkle-dev run -n mkvs-dell -c 8 -m 24Gi -- kjob lake build <Target>`。表の「再現」欄には `<Target>` だけを書く。
- Job ディレクトリは `~/git/.kjob-state/namespaces/sparkle-dev/<job>/` にある。表に書いた Job のディレクトリはすべて存在する（kjob-claude-src-dsound2-0fcc を含む）。
- 分類: **kernel 反駁**（kernel が検査した定理で否定）/ **未供給**（証明も反証もない）/ **観測**（コンパイル済みコードの実行・meta 評価・測定・読解）/ **未測定**。

---

### 1. CV の全称束縛が結論を壊す

| 項目 | full SHA | ブランチ | file:line / 宣言 | docs § | Check | Job + ログ | 再現 | 分類 |
|---|---|---|---|---|---|---|---|---|
| cvTop 反駁 | 40b176fe8082d9e0c4379526e7e313a74beb068a「CVTopCheck: FGLedgerPremisesStmtG refutes its outer hypotheses at CV := cvTop …」 | par/cvtop, par/d4*, origin/par/cvtop（origin/par/fgc-s1 には無い） | `Tests/Gen5/CVTopCheck.lean:20` `def cvTop : ConstValueRel := fun _ _ _ _ => True`、`:27` `theorem cvTop_not_functional (env : Environment) : ¬ ConstValueFunctional cvTop`、`:32` `theorem fgG_refutes_outer (hG : FGLedgerPremisesStmtG) … (h_C_EN4 …) (h_C_RK6 …) (h_C_CV4 …) (env : Environment) : False` | FG-CIRCUIT-PILOT.md には無い（Gen5 ledger 系。`scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md`） | CVTopCheck: `#print axioms` が両定理とも [propext, Classical.choice, Quot.sound] | kjob-run-src-cvtop-8246（head 40b176fe、succeeded、exit 0、mkvs-dell、33 s、`build Tests.Gen5.CVTopCheck`）。作成した agent Job は特定できなかった | `Tests.Gen5.CVTopCheck` | kernel 反駁 |
| PTlit と Signal root | bc4e180f83846bfd5c934151c1f1fca88162e996「DD4-final2: draft section Final2 (PTlit refutation, PTcorpus table/obligations, PTC census)」 | par/d4final2, par/d4cmp, par/d4stop, par/d4trace, par/d4shard*, par/d4qc* と origin の同名 | commit 自体は `scripts/gen5/CONSTVALUEE_FREEZE_DRAFT.md` だけの変更（+36 行、§Final2）。木の中の定理: `Tools/ShippingGen5PTLit.lean:168` `theorem ptlit_not_declConnect`、`:270` `theorem stmtCV_ptlit_refutes_entry (hS : FGLedgerPremisesStmtCV) …`、`:129` `stuckB_no_cvekvb`、`Tests/Gen5/PTLitCheck.lean:28` `ptnil_not_litRows`、`Tests/Gen5/CVFinalCheck.lean:143` `def PTlit` | CONSTVALUEE_FREEZE_DRAFT.md §Final2-1 | PTLitCheck（counterLoop・shift4Loop・counterEnableLoop の `stuckChk … = true` は meta 評価。含意は kernel の `stuckChk_sound`） | kjob-claude-src-d4final2-fc69（base 18af4bc3。builds に `Tests.Gen5.PTLitCheck` / `PTCorpusCheck` が exit 0 で複数回ある） | `Tests.Gen5.PTLitCheck` | 条件付きの kernel 反駁（文書: 「PTlit で偽か空虚。どちらかは示していない。EntryWitness の充足可能性は未確認」） |

不一致:
- bc4e180f は docs だけの commit である。定理は同じ木の別ファイルにある。参照としては使えるが、「commit = 定理の追加」ではない。
- 本書の「任意 PT では、行の型付けだけでソースの意味の存在を保証できない」は §Final2 と合っている。ただし根拠は「PTlit で偽、または前件が充足不能で空虚」の二択であり、無条件の反例ではない。この条件を本書に添えるのがよい。

### 2. 実行 world と環境を結んだつもりで結んでいない

| 項目 | full SHA | ブランチ | file:line / 宣言 | docs § | Check | Job + ログ | 再現 | 分類 |
|---|---|---|---|---|---|---|---|---|
| S1d `not_staticEnv` | fb3e2bc7e24d9245a45344bbc002f2b80d75a9e7「FG circuit pilot S1d-1: Supply2 (StaticEnv refuted under SetGet …)」（docs は 306716c3308326a50ff6943a472fa957ba937db9 §9） | origin/par/fgc-s1, par/fgc-s1*（多数）, kjob/kjob-claude-src-fgc-s1d-398c | `Tools/ShippingFGCircuitSupply2.lean:29` `theorem not_staticEnv {cref : ST.Ref IO.RealWorld Core.State} {E : Environment} (hsg : SetGet cref) (w : Void IO.RealWorld) : ¬ StaticEnv cref E` | §9.1（「StaticEnv は C.EN-4 の下で偽」） | Check3（FGCIRCUIT3 SIGNATURES/HYPS/AXIOMS/SNAPSHOT） | kjob-claude-src-fgc-s1d-398c（base 87c713c6、builds: `Tests.Gen5.FGCircuitPilotCheck3` exit 0） | `Tests.Gen5.FGCircuitPilotCheck3` | kernel 反駁（SetGet の下での StaticEnv の否定。FG の否定ではない） |
| S1f `MachineDefinesRun` | ca7efe1729e41002abdf2d256f61076b393a7c54「S1f-1: RunLocal (MachineDefinesRun …)」（docs 77c567d388ee677bb33081278b52e9ed6c901f15 §11） | 同上 + kjob/kjob-claude-src-fgc-s1f-e83b | `Tools/ShippingFGCircuitRunLocal.lean:26` `def MachineDefinesRun … : Prop := RunsTo (synthesizeCombinationalCore declName [] false) … w (M, D) w' → ∀ … (w1 w2 w3 w4 w5 w6 : Void IO.RealWorld), …`（読む world を run の連鎖に結んでいない） | §11.2 | Check5 | kjob-claude-src-fgc-s1f-e83b（base 07e5b53c、`Check5` exit 0） | `Tests.Gen5.FGCircuitPilotCheck5` | 観測（文の設計の欠陥を読解で発見） |
| S1g `MachineDefinesLinked`、74d5ca1d | 1b2a6216bcedf75e51629fc2b25877aa80a20ce8「S1g-1: MachineDefinesLinked (linked chain) …」。74d5ca1dfdd209821ad6f00e6519c8cfb1fad1f9 は「S1g-5: docs §12」（docs だけ、+58 行） | origin/par/fgc-s1, kjob/kjob-claude-src-fgc-s1g-ef0a ほか | `Tools/ShippingFGCircuitLinked.lean:29` `def MachineDefinesLinked … : Prop := RunsTo (synthesizeCombinationalCore …) … → ∀ (s : CoreSaved) (w1 w2 w3 w4 …), RunsTo (coreHead declName) … w s w1 → RunsTo (getConstInfo declName) … w1 ci w2 → …`。docstring: 「MachineDefinesRun (S1f) quantifies the read worlds w1 w5 w3 of the core run freely」 | §12 | Check6（SIGNATURES の mutant に「world の結び 3 種」を含む） | kjob-claude-src-fgc-s1g-ef0a（base 4948898c、`Check6` exit 0 ×2） | `Tests.Gen5.FGCircuitPilotCheck6` | 観測（修正と負対照） |

不一致: 無し。補足すると、74d5ca1d は S1g の docs commit であり、not_staticEnv（S1d）と MachineDefinesRun（S1f）はそれより前の commit にある。

### 3. opaque IO 境界で現実の成立例を供給できない

| 項目 | full SHA | ブランチ | file:line / 宣言 | docs § | Check | Job + ログ | 再現 | 分類 |
|---|---|---|---|---|---|---|---|---|
| S3m | cb92347930e19c3716c75ddbfc7d12c7610bec46「S3m: docs §63 (first blocking fields, four categories, design exits)」（docs だけ。Check53 は 50f349d3、field の事実は 6a7a26ec） | origin/par/fgc-s1, par/fgc-retro, par/fgc-s3r-merge, par/fgc-s3uv-merge, par/fgc-s3x-freeze, kjob/kjob-claude-src-fgc-s3m-d451 | `Tools/ShippingFGCircuitS3mField.lean`（`cellPrem_iff_fields`、`stderrKeeps_of_ops`、`endW_getStderr` ほか） | §63（最初の阻害 field: `ReadWorld sparkleChildCache` / `L.O.diag` → `StderrKeeps`。「矛盾は見つからなかった」「未供給」） | Check53。output.log: `FGCIRCUIT53 FIELDS: CellPrem = 10 top-level conjuncts = 16 atomic conjuncts …, the first ReadWorld sparkleChildCache`、`FGCIRCUIT53 OPAQUE: the ten primitives (ST.Prim.Ref.get/set/mkRef, …, IO.getStderr, …) are opaque`、ほか SIGNATURES/AXIOMS/OBSERVATION | kjob-run-src-fgc-m3m-322e（head cb923479、succeeded、exit 0、52 s、`build Tools.ShippingFGCircuitS3mField Tests.Gen5.FGCircuitPilotCheck53`）。agent: kjob-claude-src-fgc-s3m-d451 | `Tests.Gen5.FGCircuitPilotCheck53` | 未供給（必要条件の抽出は kernel 検査済み。MetaM の値は観測） |

不一致: 無し。本書の「矛盾や証明不能性の証明ではない」は §63 の「矛盾は見つからなかった」と合っている。

### 4. 明示状態モデルへの移行も対応境界を消さなかった

| 項目 | full SHA | ブランチ | file:line / 宣言 | docs § | Check | Job + ログ | 再現 | 分類 |
|---|---|---|---|---|---|---|---|---|
| S3n | 43a40e05362fc34d9d488f5c04c37ca7b3221890「S3n: docs §64 (E1 model, bridge, un-modelled list, cost)」（docs だけ。model b1392ca6、bridge 6cfef607、Check54 48d09d7e） | origin/par/fgc-s1, par/fgc-retro ほか, kjob/kjob-claude-src-fgc-s3n-6a59 | `Tools/ShippingFGCircuitS3nModel.lean`、`Tools/ShippingFGCircuitS3nBridge.lean`（旧 `EnvCorr` / `quietR` / `InitCorr`） | §64（2,500〜4,000 行は「見積り（粗い）」と明記） | Check54。`FGCIRCUIT54 SIGNATURES: 11 theorems (readback_depth, getStderr_keeps, getEnv_keeps, quiet_nonconst, exec_ok, corr_bind, bridge_small, …)`、EXEC/HYPS/NEGATIVE/AXIOMS | kjob-run-src-fgc-m3n-978d（head 43a40e05、succeeded、exit 0、45 s） | `Tests.Gen5.FGCircuitPilotCheck54` | 未供給（実 IO への Corr）。費用は未測定（見積り） |
| S3o `envCorr_inconsistent` / `oldQuietR_eq_true` | 59a494456763b306a555264aa2604e7a5dbb3cde「S3o: docs §65」（定理は ebfeb9e342c7c237fbd913ffa663a9020db2e635「S3o: Fix draft (refutations, RelE, toy consistency)」で追加） | origin/par/fgc-s1, par/fgc-retro ほか, kjob/kjob-claude-src-fgc-s3o-d8b8 | `Tools/ShippingFGCircuitS3oFix.lean:55` `theorem envCorr_inconsistent (mctx …) (mref …) (cctx …) (cref …) (k : String) (w : Void IO.RealWorld) (hC : EnvCorr mctx mref cctx cref k) : False`、`:65` `theorem oldQuietR_eq_true : quietR = fun _ => True` | §65（65.2 RelE/CorrE、`Toy.simultaneous_sat` は「モデル内の事実で実 pilot の証人ではない」） | Check55。`FGCIRCUIT55 REFUTE: 2 refutations as kernel theorems: envCorr_inconsistent (…), oldInit_any_world / oldQuietR_eq_true (…)`、BIND/CONTROL/SIMULTANEOUS ほか | kjob-run-src-fgc-m3o-a4da（head 59a49445、succeeded、exit 0、57 s、`build … S3nBridge S3oFix Check54 Check55`）。再実行 kjob-run-src-fgc-m3q-cdea（28dd20ff、Check55 exit 0） | `Tests.Gen5.FGCircuitPilotCheck55` | kernel 反駁（旧 EnvCorr の矛盾、旧 quietR の恒真）。toy の同時充足は観測（モデル内） |

不一致:
- 2 つの反駁定理は S3o（Check55）にあり、S3n（Check54）には無い。本書は「S3n 43a40e05、S3o 59a49445、Check54/55」とまとめて書いているので誤りではない。定理の出所は S3o と読むのが正確。
- 59a49445 の lakefile には `Tests.Gen5.FGCircuitPilotCheck55` の lean_lib 登録が無い。それでも m3o-a4da はこのモジュールをビルドして成功している。再現には影響しない。

### 5. 構文代入・値の表現が対象回路を覆わない

| 項目 | full SHA | ブランチ | file:line / 宣言 | docs § | Check | Job + ログ | 再現 | 分類 |
|---|---|---|---|---|---|---|---|---|
| 代入の負対照 | d1e6023371ff7994269559b436b50d642d47fd79「DD4-SoundS: draft §SoundS」（docs だけ、+41 行） | par/dsound2..4, par/dv*, par/dval, par/d4*, par/dd4-int と origin の同名 | `Tests/Gen5/SoundSCheck.lean:79` `theorem substS_betaS_needs_nonlam : substS (betaS (.lam …) […]) 0 (.lam …) ≠ betaS (substS …) (…)`、`:85` `substS_instForallS_needs_nonforall`。一般の `OblDenSubstS` は未証明（`oblDenSubstS_safe` は `SafeArg x` のときだけ） | CONSTVALUEE_FREEZE_DRAFT.md §SoundS-3 | SoundSCheck（48 宣言の axiom 検査） | kjob-claude-src-dsound2-0fcc（base c9ca68a2。commits.json は CalledProcessError。transcript で d1e60233 と対応） | `Tests.Gen5.SoundSCheck` | 未供給（一般補題）＋ kernel 負対照（部分の可換性） |
| PTcorpus | bc4e180f…（§1 と同じ） | 同上 | `Tests/Gen5/PTCorpusCheck.lean:24` `theorem n_recursor : (missingTable.filter …recursor).length = 15 := rfl`。行が無い key は 106（再帰子 15、Type 0 外の束縛 25（Functor/Monad 等）、証明の束縛 6 ほか） | §Final2-2 | PTCorpusCheck | kjob-claude-src-d4final2-fc69 | `Tests.Gen5.PTCorpusCheck` | 観測（測定）。件数の一部は kernel `rfl` |
| carrier 比較 | 404e597a7096a9ac50188e698fbdea0caacf9ae8「draft: Compare number fix」（2 行の数値修正。par/d4cmp の先端） | par/d4cmp, origin/par/d4cmp, kjob/kjob-claude-src-d4cmp-d273 | `Tests/Gen5/CarrierCmpCheck`（比較表は CONSTVALUEE_FREEZE_DRAFT.md の比較節。RowTypedAtV の開いた分を 18→95 から 18→99 に修正） | 比較節 §6/§7 | CarrierCmpCheck（agent 内の builds で exit 0） | kjob-claude-src-d4cmp-d273（base e37da005） | `Tests.Gen5.CarrierCmpCheck` | 観測（測定・比較） |
| Signal の停止 | 6fd58e9eae054369564be3e46961d920648d3e70「Stop section: fix instance count」（docs 1 行） | par/d4stop, par/d4trace, par/d4cmp と origin の同名 | §Stop の表: 再帰子 15 → 15（減少 0）。再帰子に到達する root は 232 → 224（/235） | §Stop | PrimResidueStop*（M1..M4, Sig） | kjob-run-src-d4stopx-8708（head 6fd58e9e、succeeded、exit 0、mkvs-macpro、7859 s） | `Tests.Gen5.PrimResidueStopSig`（全体は `PrimResidueStopLib … PrimResidueStopSig` の 7 target） | 観測（測定） |
| 再帰子の出所 | e37da00537067afc8e0673b84f2153874bb75db3「DD4-final Q-A (i): section Trace」（docs、+59 行） | par/d4trace, par/d4cmp と origin の同名 | §Trace の表: 段階 1（Signal を停止）で再帰子 15、段階 3 で 5 | §Trace | PrimResidueTrace*（agent 内の builds で exit 0） | kjob-claude-src-d4trace-27fb（base 6fd58e9e） | `Tests.Gen5.PrimResidueTraceSig` | 観測（測定） |

不一致:
- **「一般代入補題が現規則では成立しない場合」は根拠より強い。** d1e60233 自身は「一般の代入補題は偽になりうる（反例の形は上記。具体の PT での導出の反例までは構成していない）」と書いている。kernel で示したのは構文演算 `substS` と `betaS` / `instForallS` が可換でない例だけで、補題そのものの反例ではない。分類は「未供給（反例の候補あり）」にするのが正確。
- 引用された 5 つの SHA（d1e60233, bc4e180f, 404e597a, 6fd58e9e, e37da005）はすべて `CONSTVALUEE_FREEZE_DRAFT.md` だけの commit である。特に 404e597a は 2 行の数値修正であり、「carrier 比較」の本体は par/d4cmp のそれより前の commit にある。

### 6. 証明項の共有破壊と誤った性能測定

| 項目 | full SHA | ブランチ | file:line / 宣言 | docs § | Check | Job + ログ | 再現 | 分類 |
|---|---|---|---|---|---|---|---|---|
| 28 GB bad_alloc（S2b） | 5dc8972fec0c6780c71674ccf091b501df833e41「S2b: Check25 share ladder, docs §30」（比較本体は 35f0cf2daa25f0fe819f4e1f48b4fcf76d0bc2cd「native (sharing-preserving) evaluators, probe, comparison old vs native」） | origin/par/fgc-s1, par/fgc-retro, par/fgc-s2* ほか, kjob/kjob-claude-src-fgc-s2b-b60e | `instE` が共有を壊す。§30.3: 新方式は「60 509 節点、128 s、ピーク 4.2 GB、完走（旧は 28 GB で bad_alloc）」 | 最初の記録は §23.6（S1w2、9e6556e9a9cb10435b1ec7ee19807eea0ce10cf6、`ulimit -v 28000000`）、比較は §30.3、Check25 の出力は §30.5 | Check25 SHARE-LADDER（k = 16 で木 524 281 節点、DAG 38 節点） | kjob-claude-src-fgc-s2b-b60e（`Check25` exit 0）。bad_alloc は kjob-claude-src-fgc-s1w2-20ce と s2b-b60e の history jsonl に記録がある | `Tests.Gen5.FGCircuitPilotCheck25` | 観測（測定） |
| 非同期の宣言登録（S2q） | 64742f1a16fb392248630f968da885fc2da186cc「S2q: docs wording」（修正本体は 157b75c52fe3288eb41813ad862fabd86759bfb0「Run: synchronous kernel call …」、docs は e93f5a24） | origin/par/fgc-s1 ほか, kjob/kjob-claude-src-fgc-s2q-514d | `deriveRootT` の計測を `Environment.addDeclCore`（同期）に変更。32 ms → 7283 ms | §43.4、§36′ の訂正注、§45′.4 | Check38 | kjob-claude-src-fgc-s2q-514d（`Check38` exit 0） | `Tests.Gen5.FGCircuitPilotCheck38` | 観測（測定の訂正） |
| S2t/u と約 6.9 秒 | 9503bb49ca506eb1d251d2d3c0821d4a77c3f91c「Merge S2u (e1ec18be …) onto e3136673」。S2t は 87d8e3cde0d8b70b8c19934ba74353c659e478e0（merge e31366737c63fedebf2ae9882fcd9f4220b2c339） | origin/par/fgc-s1 ほか, kjob/kjob-claude-src-fgc-s2x-05d7 ほか | §45.3: `kernel（同期 addDeclCore）6882 ms`、DAG 737 294、ピーク RSS 3 279 072 kB。`hftObCDT_T : ∀ env (hΔ …) (hΓ …) (hrec : RecFact env), HftObCDT env`（条件付き） | §45（S2t）、§45′（S2u） | Check40 / Check41、`Tools.ShippingFGCircuitS2tHftOb` | kjob-claude-src-fgc-s2t-523b（`S2tHftOb` exit 0 ×2）、kjob-claude-src-fgc-s2u-7101、統合: kjob-run-src-fgc-s2rt-e89d（e3136673、exit 0）、kjob-run-src-fgc-s2tu-407c（9503bb49、exit 0、175 s） | `Tools.ShippingFGCircuitS2tHftOb Tests.Gen5.FGCircuitPilotCheck41` | 観測（1 回の測定。条件付きの導出） |
| S3a2 の internE | （本書は SHA を書いていない）定義は 11c5a539（S2z）、遅延は d64e65af3389f86aeec94ab4c7abc0a7dc0631e3「S3a step1b draft (build did not finish in 20+ min: internE walks the shared callee terms as a tree; stopped by the coder)」、修正は 6a871de287aae150dda132c3e57e10543cc8c61d「S3a2: internE memoised on the subterm …」 | origin/par/fgc-s1, kjob/kjob-claude-src-fgc-s3a2-4a3a | `Tools/ShippingFGCircuitS2zGenTables.lean:69`（6a871de2 / 615b4b90）`partial def internE (e : Expr) : G Nat := do` | §50.1 | Check45 | kjob-claude-src-fgc-s3a2-4a3a（base d64e65af、12 builds exit 0）、統合 kjob-run-src-fgc-m3a-29b5（58328c91、exit 0） | `Tests.Gen5.FGCircuitPilotCheck45` | 観測 |

不一致:
- 28 GB の bad_alloc が最初に記録されたのは S1w2 §23.6（9e6556e9）である。S2b（5dc8972f）は旧方式との比較と対策の段階にあたる。根拠として S2b を挙げることはできるが、「症状が出た段階」は S1w2。
- internE が DAG を木として歩いた問題が見つかったのは S3a（d64e65af）で、S3a2（6a871de2）はその修正である。本書の「S3a2 の internE も DAG を木として歩いていた」は段階名がずれている。この事例には SHA も書かれていない。
- 9503bb49 は S2u の merge であり、6.9 秒の測定は S2t（87d8e3cd、§45.3）。「S2t/u 9503bb49」は両方を含む commit なので誤りではない。

### 7. 検査器・生成器にもバグがあった

| 項目 | full SHA | ブランチ | file:line / 宣言 | docs § | Check | Job + ログ | 再現 | 分類 |
|---|---|---|---|---|---|---|---|---|
| 枝の選択（instance を見ない）、α 同値 cache（S2q） | 64742f1a…（§6 と同じ）。修正本体は 4eb8e0ad32012ea10a053948cbe19fb81bf40590「generator: strict instance-form checks」、fc154719f750b59dd73f4881fb9171325da9e52a「binder name/info taken from the quoted term」 | origin/par/fgc-s1 ほか | `S2iGen` / `S2iRun` | §43.2（kernel の「application type mismatch」で発覚） | Check38 | kjob-claude-src-fgc-s2q-514d | `Tests.Gen5.FGCircuitPilotCheck38` | 観測（kernel が拒否したことで発見） |
| α 同値 cache の残り（S2u） | e1ec18bed132f6a27fad79ed6986192ec0f01d23（9503bb49 に merge） | 同上 | `S2bGen.qE` の cache を厳密な Expr 一致に変更 | §45′.3（Check41 ALPHA の accept が「declaration type mismatch」になった） | Check41（fixed_dt accept/reject） | kjob-claude-src-fgc-s2u-7101、kjob-run-src-fgc-s2tu-407c | `Tests.Gen5.FGCircuitPilotCheck41` | 観測 |
| S2w 名前による証明判定 | 6aaec627e220bfe48fb8c5f9be56253a476d9c60「Merge S2w (34c41a18: FGCircuitCmp proof irrelevance by type, standard-instance BEq/OfNat, regression controls …)」 | origin/par/fgc-s1 ほか, kjob/kjob-claude-src-fgc-s2x-05d7 | `Tests/Gen5/FGCircuitCmp.lean`（`_proof_` の名前による判定を削除し、`Meta.isProof` で判定） | §47.1–47.3 | FGCircuitCmpRegress ほか | kjob-claude-src-fgc-s2w-2b9d、統合 kjob-run-src-fgc-s2uw-8e23（6aaec627、exit 0） | `Tests.Gen5.FGCircuitCmpRegress` | 観測 |
| S2x ローカル BEq instance | 0afddb9234ca42180a9dd48b17427757df8b19e5「S2x: docs §47.5」（コードは f786d1e9「litBool? uses the fixed standard BEq Nat instance; regression control with badBEq …」） | origin/par/fgc-s1 ほか, kjob/kjob-claude-src-fgc-s2x-05d7 | `litBool?` が `stdBEqNat` を使う | §47.5 | FGCircuitCmpRegress（`FGCIRCUITCMPREGRESS controls: all passed …`） | kjob-claude-src-fgc-s2x-05d7 | `Tests.Gen5.FGCircuitCmpRegress` | 観測 |
| S2v merge 後の修正 | 6a331dc5ee49818fdfdda202b7a9c5d330587e5d「FGCircuitCmp: normalise the propositions of the last proof pass too (… found by Check42 root_states after the S2v merge); regression controls 7」 | origin/par/fgc-s1 ほか, kjob/kjob-claude-src-fgc-s2y-3aae | merge 8296b8f3 で `Tests/Gen5/FGCircuitPilotCheck42.lean:558: root_states: type is NOT the expected statement` | §46.4、§47 | Check42 | 失敗: kjob-run-src-fgc-m2v-0422（8296b8f3、failed、exit 1）。修正後: kjob-run-src-fgc-m2v-05d5（6a331dc5、succeeded、exit 0、55 s） | `Tests.Gen5.FGCircuitCmpRegress Tests.Gen5.FGCircuitPilotCheck42` | 観測（失敗 Job → 修正 → 成功 Job の記録がそろっている） |

不一致: 無し。補足として、0afddb92 と 64742f1a は docs の commit で、コードの修正は上に書いた別 commit にある。

### 8. artifact の観測を意味保存の橋と取り違えかけた

| 項目 | full SHA | ブランチ | file:line / 宣言 | docs § | Check | Job + ログ | 再現 | 分類 |
|---|---|---|---|---|---|---|---|---|
| S3r | b8fbe4916dbd05a55b2c4675eaf88974d232a69a「Merge S3r (closed pilot artifact, kernel checks, Check56, §68) onto par/fgc-s1 8bb4efd4 (S3s docs)」 | origin/par/fgc-s1, par/fgc-retro, par/fgc-s3r-merge, par/fgc-s3uv-merge, par/fgc-s3x-freeze, kjob/kjob-claude-src-fgc-s3t-09bf 以降 | `Tools/ShippingFGCircuitS3r{Gen,Artifact,Kernel,Obs}.lean`（`pilotB0` 256 文、`pilotS0` 89 文） | §68.3（`optimizeModule` は partial def、`String.all` は `decide +kernel` で止まる）、§68.4（確立した事実と観測の区別） | Check56: `FGCIRCUIT56 KERNEL: 7 facts (hierBinds b0; hierRefineCheck b0 b0; …)`、`FGCIRCUIT56 OBSERVATION: … compared with BEq: (b, D) == (pilotB0, pilotD0) and checkedOpt…` | kjob-run-src-fgc-mg3r-8756（head b8fbe491、succeeded、exit 0、194 s）。agent: kjob-claude-src-fgc-s3r-6dfb | `Tests.Gen5.FGCircuitPilotCheck56` | 観測（S0 と optimizer の出力の一致）と kernel の事実（閉じた項の検査）が分かれている |
| 17 レジスタ、assign/inst の移送補題 | 同上（事実の記録は S3s 8bb4efd4d1dc0906a7a6546cbc1c99c55f981c79 / S3q 28dd20ff06181b6b51ce381c97f7fe018928a8f3） | 同上 | `combStmtI`（`Tools/ShippingHierSVSoundness.lean:404`）は `.assign` と `.inst` だけを true とする | §67.9「【S3s 確定】」（3653 行、3849 行。「[読]」= 読解による確認） | — | kjob-claude-src-fgc-s3q-f971 / s3s-4466 | — | 観測（読解） |

不一致:
- 「階層 top は 17 レジスタを持ち、assign/inst のみの既存 SV 移送補題はそのまま使えない」は §68（S3r）ではなく §67.9（S3s/S3q）の記録である。b8fbe491 は 8bb4efd4 の上に作った merge なので、SHA としては含まれる。段階名だけがずれている。

### 9. 局所成果の積み上げが一般 FG の完成に結び付かなかった

| 項目 | 根拠 | 分類 |
|---|---|---|
| FG 75 / T1 57 が変わっていない | FG-CIRCUIT-PILOT.md の各節に「台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）」とある（§68 冒頭、§45 冒頭など）。§46.6 / §48: 「ledger FG 75 / -0」（26fb676a, 0ce62d64）。§68: 「1 artifact の証明書は局所成果であり、台帳の減算ではない」 | 観測（台帳の記録） |
| FG 約 100 → 75 | 本書自身が「ユーザーの把握では」と書いている。既存台帳からの集計は今回行っていない | 未測定 |

不一致: 無し（主張は記録と合っている）。

---

### 「何が進んだか」節（22 行目）の照合

| 項目 | full SHA | file:line / 宣言 | docs § | Check / Job |
|---|---|---|---|---|
| `checkComb_sound` | 6a59d36e6e90ec4c2fb439962b05e81228317127「S3t: checkComb and checkComb_sound …」 | `Tools/ShippingFGCircuitS3tComb.lean:391` `theorem checkComb_sound (s : CSrc) (m : Module) (h : checkComb s m = true) (V : Nat → Nat) (mems : MEnv) (env : Env) (hin : …) : ∃ env', evalAssigns (declWidth m) mems m.body env = some env' ∧ …` | §69（S3t） | Check57。kjob-run-src-fgc-m3t-40f6（8ed3fcc4、exit 0）。agent kjob-claude-src-fgc-s3t-09bf |
| `ofData_sound` | 11b9e152b7daede14e9a33cb53e2bde9ba861435「S3v: bridge ofData_sound …」 | `Tools/ShippingFGCircuitS3vBridge.lean:283` `theorem ofData_sound (d : MachineData) (hss : d.ss.length = 0) (V : Nat → Nat) (x : HList (tys d.ss)) …` | §71（S3v） | Check58v。agent kjob-claude-src-fgc-s3v-389a |
| `k0_childFn` | 965aba7d7eaf1d0e65d25bd0b23b298948028ca3「S3v: k0_childFn … proved」 | `Tools/ShippingFGCircuitS3vChild.lean:36` `theorem k0_childFn : ChildFn pilotK0 (childRange kd0) (childValue httpGetByte.machineSource kd0.bsIn defaultDomain)` | §71 | Check58v: `FGCIRCUIT58V SCOPE: ONE closed child (pilotK0 = httpGetByte, 88 statements) for ALL inputs in its range, no run premise …` |
| 615b4b90 と m3uv-1cf9 | 615b4b90b8d558b0865074ab64a1bb69cd2b69bc「S3t Spec docstring: SrcEq pins the source fields, not the claims portNames/kidMod」（a1bb4857「Merge S3v … onto S3u 7926cae0」の直後） | — | §70.4（e620c29c が受理済み freeze として記録） | kjob-run-src-fgc-m3uv-1cf9（head 615b4b90、succeeded、exit 0、171 s、Check57 と Check58v をビルド） |

不一致:
- **`checkComb_sound` と Check57 は S3t（6a59d36e / 7da493ad、§69）の成果であり、S3u/v ではない。** `ofData_sound` と `k0_childFn` と Check58v は S3v。S3u（§70）は freeze 境界 P1-1/P1-2 の段階。「S3u/v」は「S3t/S3v（S3u の freeze 境界を含む）」とするのが正確。615b4b90 の題名は「S3t Spec docstring」だが、木には S3t/u/v がすべて入っており、m3uv-1cf9 がこの SHA で Check57/58v の成功を記録している。SHA と Job の対応は正しい。

---

### 進行中 Job の最終状態（`kjob result --namespace sparkle-dev JOB`、読み取りのみ）

| Job | phase | base_head | end_head | dirty | candidate commits | 検証 |
|---|---|---|---|---|---|---|
| kjob-claude-src-fgc-s3w-ac60 | wait_agents（finished_at 無し） | 615b4b90 | 1ac6104cf24ddc040f0af3ba7dd073abb029bd98「S3w: FragW bridge (bool-let boolInput) and k1_childFn draft」 | **true** | 137c3bee「checkCombN … and checkCombN_sound」、6fa8d941「checkCombN accepts pilotK1 (kernel), controls」、1ac6104c | 1ac6104c を含むのは kjob/kjob-claude-src-fgc-s3w-ac60 だけ（par/ と origin には無い）。この SHA の run Job は無い。k1_childFn は draft で、ビルドされたかどうかは確認していない。worktree に未コミットの変更がある |
| kjob-claude-src-fgc-s3z-6255 | wait_agents（finished_at あり） | 8d587684 | 8d587684d29673f424bf9c1fff40df70bd678f5e（base と同じ） | false | 無し | 成果となる commit は無い |
| S3y: kjob-claude-src-fgc-s3y-7f78 | response_ended | 8d587684 | 7da2992bc0130429ac237af48b91d8ca3d16ba8c「S3y: docs §73」 | false | ea74039b, b972ae8f, 62231044, f29ac912, d01ab0cb, 8fbf8ff2, 7da2992b | kjob-run-src-fgc-m3y-3010（7da2992b、exit 0、Check60: CONTROLS/SCOPE/SIGNATURES/AXIOMS/SIZE） |
| S3y2: kjob-claude-src-fgc-s3y2-6b9b | response_ended | 7da2992b | 8cf6beef330b751b79911cd243694b637df21d61「S3y2: docs §73 addendum, wording and unconnected ledger」（= origin/par/fgc-s1 の先端、par/fgc-retro にも含まれる） | false | debf37a1, e60ddabd, dd55b630, e0c0e218, 8ce5310d, 8cf6beef | kjob-run-src-fgc-m3y2-794b（8cf6beef、succeeded、exit 0、40 s、`build Tools.ShippingFGCircuitS3yGen Tools.ShippingFGCircuitS3yEntry Tests.Gen5.FGCircuitPilotCheck60`。FGCIRCUIT60 CONTRACT/CONTROLS/SCOPE/SIGNATURES/AXIOMS/SIZE）。定理は `Tools/ShippingFGCircuitS3yGen.lean:138` `checkData_sound`、`Tools/ShippingFGCircuitS3yEntry.lean:48` `certifiedEntryC_sound`。docs §73 |

ほかの記録: kjob-run-src-fgc-m3x-913d（e620c29c）は `S3vBridge.lean:31` の二重 doc comment で失敗している（exit 1）。8d587684 で修正し、kjob-run-src-fgc-m3x2-aeb9 は exit 0。

## 付録 B: 台帳の内訳（coder、2026-11-08）

記録された値だけを数えた（推測なし）。FG 台帳の最新は par/fg-ledger-sync 8649968e（§12.24、FG 75）、T1 は par/t1-ledger-sync d91bab13（§12.6、T1 57）。


読んだもの（読み取りのみ。build・編集なし）:

- FG 台帳 `scripts/gen2/PREMISE_LEDGER.md` の最新版 `par/fg-ledger-sync` 8649968e（§2, §4, §9.1, §9.5, §10, §11, §12〜§12.24）
- T1 台帳 `scripts/gen3/PREMISE_LEDGER.md` の最新版 `par/t1-ledger-sync` d91bab13（§12〜§12.6）
- `scripts/gen2/LEDGER_SHORTEN_PLAN.md`（628f30c5）、`scripts/gen5/LEDGER_CROSSCOUNT_DECISION.md`（392dc221）、`scripts/gen5/BINDER_EXIT_CENSUS.md`（2ce38c69）は件数の照合にだけ使った
- coder セッションの記録（`ee390511-….jsonl`）にある「台帳: FG N / T1 M（今回 …）」の行。異なる行は 585 種類。予定・見込み・申請の行は除き、受入値が変わった行だけを使った

数え方: FG の「現在値」は台帳 §2 の定義（§8.2 の 110 行表で未解消の行数。§12.1 と §12.8 で計上した追加行を含む）を使う。比率や推定は入れていない。日付は台帳コミットの日付で、括弧内はセッション記録の UTC 時刻。

### 0. 出発点

| 値 | 記録 | 出典 |
|---|---|---|
| FG 146 | 段 1 の前提ブロック数（A 28 + B 26 + C 55 + D 37） | FG 台帳 §1, §2（d38c7e87, 2026-10-31） |
| FG 110 | 146 − 36。別名欄に「同じ型」と書かれている組をまとめた（重複の統合 19 組、36 行を除いた） | FG 台帳 §4 |
| T1 62 | 71 行のうちリーフ 62（TRUSTED 1 + 入力 2 + 証明義務 56 + 監査 3） | T1 台帳 §11.1（51ebec20） |

「約 100」という値は、受入値の出発点としては記録されていない。100 前後の値は 2026-11-01〜02 の FG 102 / 103 で、出発点は 110（重複統合の前なら 146）である。

### 1. 時系列の表（FG）

分類の記号:

- **P** 証明による除去。新しい Lean の定理か Check で、その前提が最終の文に残らなくなった
- **U** 不要な binder の除去。既存の root が、もともとその binder を取らないことを Check で確認しただけ（新しい証明はない）
- **D** 重複計上の統合。別の行（T1 台帳の行を含む）で数えているので外した。Lean は変わっていない
- **N** 非リーフの置き換え。新しい Lean で、binder を既存の FG 行や T1 行に置き換えた。台帳には「非リーフの除去で、リーフは動かない」「証明の進捗ではない」と書かれている
- **R** 数え方の規則による除去、または数え直しの訂正
- **+** 前提の追加

| # | 日付（記録時刻 UTC） | FG | T1 | 動いた行 | 分類 | 記録されている理由 | 根拠 SHA / Issue |
|---|---|---|---|---|---|---|---|
| 1 | 10-31（15:55） | 110 → 106 | 59 | −C.RK-5, −D.T-5, −D.T-8, −D.T-9（承認 note では −4） | P | 流れ 1: `runReads_of_run` / `callTie_of_run_*` が実際の run から前提を置き換えた | e6d8e55b（kjob/flow1-b）、sparkle-gen5-dg-closingrun seq 5756 |
| 2 | 10-31（16:06） | 106 → 107 | 59 | D.T-5 を戻した（+1） | R（訂正。件数が増えた） | D.T-5 は §4 で除いた 36 行の 1 つで、110 行表に入っていない。110 − 3 = 107 | c9525021（§2, §9.1） |
| 3 | 11-01（00:04） | 107 → 105 | 57 | −C.SM-2, −C.SM-4 | P（固定 carrier が条件） | 候補 A。proof-accept 合格 | 628bc5d3、sparkle-gen5-dg-sem |
| 4 | 11-01（00:09） | 105 → 104 | 57 | −C.SM-3 | P（同上） | SM3。proof-accept 合格 | 4cade1d0、sparkle-gen5-dg-acc |
| 5 | 11-01（00:14） | 104 → 102 | 57 | −C.AC-2, −C.AC-3 | P（同上） | CKIT。proof-accept 合格 | 4bc671dd、sparkle-gen5-dg-kit。台帳 §12 は 3b459613 |
| 6 | 11-02（11-01 13:36〜16:24） | 102 → 103 | 54 | +SigTyClosed, +InstSFieldsDet, −C.CV-1 | +2 / P 1 | 名前付きの環境条件を 2 つ追加した。C.CV-1 は、ユーザー判断 D4 で文を `LetQuoteEqC` に改めたあと、witness の証明で外した | 0e7b1723 / 4d6b9719、bdb4d79b / 206c39a2、65c5f644。台帳 §12.1（44889946） |
| 7 | 11-02（00:53） | 103 → 102 | 56 | −C.SM-5 | R（R0-B） | 数え方 R0 の承認。材料の C.SM-3 / C.SM-4 は解消済みで、`srcCausal_of_acc_unfold` で組み立てられる。R0-A は表示の分割だけで、件数は変えない（リーフ 72 / 非リーフ 30） | LEDGER_R0_FREEZE c4451031。台帳 §12.2（6a8ec786） |
| 8 | 11-02（07:45） | 102 → 95 | 56 | −C.RT-1, −C.RT-3, −C.RT-4 | P（リーフ） | U1。前提閉包が、数えた行だけに帰着することを Check で示した | 912022f1、sparkle-rt-u1 |
| 〃 | 〃 | 〃 | 〃 | −D.E-1, −D.E-2, −D.E-5, −D.E-9 | P（リーフ） | U-A1。残る D.E-6 / 7 / 8 から導ける派生行になった | 0d979146、sparkle-aud-ua1。台帳 §12.3（9e818182） |
| 9 | 11-02（08:18） | 95 → 94 | 56 | −D.E-6 | P（リーフ） | U-A2 `auditE6_of_defines'` | fc6c193b、sparkle-aud-ua2。§12.4（2c32314d） |
| 10 | 11-03 | 94 → 94 | 54 | なし | — | B4 の範囲を明記した（ユーザー判断 (3)） | §12.5（ab3aeceb） |
| 11 | 11-03（01:05） | 94 → 93 | 55 | −D.E-3（T1 側は +T1L-75） | P（リーフ） | U-A4/5 `auditE3B3_of_t1hyp_run`。D.E-4 は B3/B4/B5 の束なので残した | f5de62a0、sparkle-aud-ua4。§12.6（8efa66ff） |
| 12 | 11-03（02:13） | 93 → 92 | 55 | −A.P-22 | D（非リーフ） | T1L-03 の前件。FG 側に独立した binder がない | b312b0df、sparkle-ledger-nonleaf。§12.7（ae451af4） |
| 13 | 11-03（02:43） | 92 → 94 | 57 | +N1-a, +N2-b, +N3-b RawNodePh, +N3-b NormNodePh, +RecRulePhU / −C.RT-2, −C.CV-2, −C.CV-3 | +5 / P 3（置き換え） | ユーザー判断 (A)。`readerTrace_final` が使う、明示した小さな仮定を計上し、reader の正しさの 3 行を消した | 378f8e31、sparkle-gen5-dg-readertrace。§12.8（c1b731f3） |
| 14 | 11-03（03:31） | 94 → 92 | 57 | −D.E-7, −D.E-8 | P（リーフ） | U-A3g `auditE7_e8_of_run` | a7baff1d、sparkle-aud-ua3g。§12.9（e5025b28） |
| 15 | 11-03（05:42） | 92 → 91 | 57 | −B.F-4 | P（リーフ。first-gate fragment の範囲だけ） | hS → hQ の橋 | 66d13eef、sparkle-gen4-fallback-supply。§12.10（8f2c1ded） |
| 16 | 11-05（11-04 22:50） | 91 → 88 | 57 | −A.P-26, −C.CR-1, −A.P-24 | N | HORD_RUN。`hord` / `hrow` を証明の中で出す。A.P-24 は T1 の行に置き換えた。台帳には「重ねて数えていた非リーフの行の除去で、証明の進捗ではない」と書かれている | bb050d37（承認 bca5746e）、sparkle-ledger-hord-run。§12.11（c2e32362） |
| 17 | 11-05（11-04 23:37） | 88 → 87 | 57 | −C.RK-1 | P（リーフ） | `h_C_EN4` の連言から `ReadKeeps` を出し、文から binder を除いた（新旧の文は同値） | d436536b（承認 113cd51b）、sparkle-ledger-rk1。§12.12（275f1739） |
| 18 | 11-05（00:39） | 87 → 85 | 57 | −C.CV-5 | U（リーフ） | root `readerTrace_final` がもともと束縛変数に持たない | sparkle-ledger-ac9cv5。§12.13（7816a33c） |
| 〃 | 〃 | 〃 | 〃 | −C.CV-6 | P（リーフ） | `readerTrace_final_b1` | 9ab07ab8（承認 3cd32441） |
| 19 | 11-05（01:23） | 85 → 84 | 57 | −C.AC-9 | P（リーフ。kit の固定） | AC9KIT `accServed0_of_cover_gatesK` | 04db3763、sparkle-ledger-ac9。§12.14（815a6f58） |
| 20 | 11-05（08:41） | 84 → 83 | 57 | −D.T-2 | U（非リーフ） | ND root が `CallOutRange` を取らないことを Check で確認した | 8d0e5ad8、sparkle-ledger-dt2。§12.15（36484663） |
| 21 | 11-05（09:47） | 83 → 81 | 57 | −D.T-1, −D.D-3 | P（リーフ。scoped intermediate） | GPFIX。ユーザー判断 A で `GP := genGP` に固定し、`h_D_T1` を導出した | ad239809、sparkle-ledger-gpfix。§12.16（aa32df14） |
| 22 | 11-05 | 81 → 81 | 57 | N4-a `LamTelescopeN` を候補として登録 | —（数えていない） | 最終 FG が取り込めば +1 | sparkle-gen4-param-ftheta。§12.17（1bf1d022） |
| 23 | 11-05（10:41） | 81 → 80 | 57 | −C.SM-7 | N | `hT2Tie_of_genGP`。既存の行だけから出した | 7a3779e6、sparkle-ledger-sm7。§12.18（ed87b24f） |
| 24 | 11-05（11:54） | 80 → 79 | 57 | −A.P-17 | N | ND 部品と下流の再配線（`dec` を各段で導出） | 7b2a4797 + 72e2b9ff、sparkle-ledger-ap17。§12.19（1276988b） |
| 25 | 11-05（13:54） | 79 → 78 | 57 | −A.P-12 | D（非リーフ。cross-ledger の一意計上） | T1L-11/12 の連言としてだけ使われる。Lean は変えていない | 59e43393、sparkle-ledger-ap12。§12.20（383aa2e8） |
| 26 | 11-05（14:00） | 78 → 77 | 57 | −C.CR-4 | N | `t1HypND_of_rows`。既存の行から `T1HypND` を作った | f9dbc699、sparkle-ledger-cr4。§12.21（2a8946ae） |
| 27 | 11-05 | 77 → 77 | 57 | なし | — | D.D-4（CV）の欠陥を認定した。組み立ての前に CV の固定が要る | 40b176fe。§12.22（bac6a3ac） |
| 28 | 11-05（14:31） | 77 → 76 | 57 | −C.DG-1 | P（リーフ。台帳には「C.AC-4 から導く統合として数える」とある） | `genGP_fields` ほか | 5c65a5cb、sparkle-ledger-dg1。§12.23（e3bdd376） |
| 29 | 11-05（14:34） | 76 → 75 | 57 | −C.SM-1 | P（リーフ。`initsOf` の固定） | FGLedgerPremisesStmtH。`hs` を `dataOfAt_sound` で与えた | 0fceecd7、sparkle-ledger-sm1。§12.24（8649968e） |

R0 の内訳（リーフ / 非リーフ）は §12.2 の 72 / 30 から §12.24 の 54 / 21 まで、どの節でも記録の数と合っている。

### 1b. 時系列の表（T1）

| 日付 | T1 | 行 | 分類 | 根拠 |
|---|---|---|---|---|
| 10-31 | 62 → 59 | −T1L-20, −T1L-22, −T1L-24 | P | U18 82cb67a6 |
| 10-31 | 59 → 58 | −T1L-28（申請は −2。T1L-27 は認められなかった） | P | U-B1 83820d32、sparkle-gen3-data-supply |
| 11-01 | 58 → 57 | −T1L-40 | P | K1 861c90ab（proof-accept） |
| 11-01 | 57 → 54 | −T1L-52, −T1L-58, −T1L-59（コンパイラの関数を全域化して定理にした）。T1L-54/55/56 は置き換え（−3 +3 で正味 0） | P | 965fe51b、ad5f7704。T1 台帳 §12 |
| 11-02 | 54 → 55 | +T1L-72 EqvAtom | + | f3a483bd。§12.1 |
| 11-02 | 55 → 56 | T1L-54 → T1L-73（±0）、+T1L-74 | + | 6aa30e51。§12.2 |
| 11-02 | 56 → 55 | −T1L-04 hrow（コンパイラの検査 G' を追加した） | P | 877c1498。§12.3 |
| 11-03 | 55 → 54 | −T1L-18（case X の枝だけ） | P | e4d3087d。§12.4 |
| 11-03 | 54 → 55 | +T1L-75 hLeafAlias | + | f5de62a0。§12.5 |
| 11-03 | 55 → 57 | +T1L-76, +T1L-77。T1L-74 の置き換え（±0） | + | 378f8e31。§12.6（d91bab13） |

T1 の内訳は、除去 10、追加 5、置き換え 5 行（正味 0）。62 − 10 + 5 = 57 で合う。11-03 以降、T1 は 57 のまま変わっていない。

### 2. 分類ごとの合計（FG、110 → 75）

| 分類 | 行数 | 行 |
|---|---|---|
| P 証明による除去 | **−31** | 流れ 1 の 3、C.SM-2/3/4、C.AC-2/3、C.CV-1、C.RT-1/3/4、D.E-1/2/5/9、D.E-6、D.E-3、C.RT-2、C.CV-2/3、D.E-7/8、B.F-4、C.RK-1、C.CV-6、C.AC-9、D.T-1、D.D-3、C.DG-1、C.SM-1 |
| 　うち固定 carrier・scoped などの条件つき | （内数）−12 | C.SM-2/3/4、C.AC-2/3（GenData-kit の採用が条件）、C.AC-9、D.T-1、D.D-3（`GP := genGP` の範囲）、C.SM-1（`initsOf` の固定）、C.DG-1（統合として数える）、B.F-4（fragment の範囲だけ）、C.CV-1（文を改めたあと） |
| 　うち仮定 +5 と引き換えの置き換え | （内数）−3 | C.RT-2、C.CV-2、C.CV-3（§12.8） |
| U 不要な binder の除去 | **−2** | C.CV-5（リーフ）、D.T-2（非リーフ） |
| D 重複計上の統合 | **−2** | A.P-22、A.P-12（どちらも非リーフ。Lean は変えていない） |
| N 非リーフの置き換え | **−6** | A.P-26、C.CR-1、A.P-24、C.SM-7、A.P-17、C.CR-4 |
| R 数え方の規則（R0-B） | **−1** | C.SM-5 |
| R 数え直しの訂正（件数が増えた） | **+1**（記録では −4 のあと +1） | D.T-5。流れ 1 の承認 note は −4 で、後から +1 と訂正した。上の P の「流れ 1 の 3」は訂正後の数 |
| + 追加 | **+7** | SigTyClosed、InstSFieldsDet、N1-a DeclValuePh、N2-b PackTupleInputsBridge、N3-b RawNodePh、N3-b NormNodePh、RecRulePhU |
| どれにも当てはまらないもの | **0** | — |

突き合わせ:

- 訂正後の数で数えると、110 − 31 − 2 − 2 − 6 − 1 + 7 = **75**。
- 記録どおりの数で数えると、110 − 43（除去の記録。D.T-5 を含む）+ 1（訂正）+ 7（追加）= **75**。
- 146 から数えると、146 − 36（段 1 の重複統合、D）= 110。そこから上と同じで 75 になる。
- リーフ / 非リーフで分けると、102（72 / 30）からリーフは −23 +5 = −18 で 54、非リーフは −9 で 21。合わせて 75。
- 差は残らない。

参考: 台帳が自分で「証明の進捗ではない」と書いている除去は、D 2、N 6、U のうち D.T-2 の 1、R0-B の 1 で、合わせて 10 行。リーフの P が 31 行（R0 の記録が始まる前の 9 行を含む）、リーフの U が 1 行（C.CV-5）。

### 3. 記録どうしの食い違い

1. **流れ 1 の −4 と −3。** sparkle-gen5-dg-closingrun の承認 note（seq 5756）は「110 → 106」で、記録は 2026-10-31 15:55。台帳 §2 / §9.1 は 107 としている（D.T-5 は 110 行表に入っていない）。16:06 に「FG 107（前回記録の −4 を訂正）」と直された。§9.1 にも、承認 note の値を引用として残してある。
2. **古い基準値を使った note。** T1 側 Issue（sparkle-gen3-t1-assembly、seq 5743 / 5745、10-31 19:39 頃）の note は「FG 110 / T1 62」と書いている。同じ時点の受入値は FG 107 / T1 58。ほかにも、11-03 05:06 の parametric の調査資料が「受入値 FG 93 / T1 55」と書いている（その時点の受入値は FG 92 / T1 57）。
3. **受理前の減算を現在値に入れた note。** sparkle-rt-u1 の note（11-01 21:06 と 23:01）は「FG 100 / T1 55（今回 FG −3、受理待ち）」と書いている。同じ時刻の reviewer 側の記録と台帳は FG 103。U1 の −3 が実際に入ったのは 11-02 07:45（FG 95）。
4. **FG 74 の誤記。** 11-07 の FGC パイロット文書 §46.6 の初版は「FG 74（今回 FG −1、hlink = D.D-3）」と書いた。reviewer が「D.D-3 は §12.16 で減算済み」と訂正し、FG 75（−0）に戻した。受入値は 75 のまま。
5. **D.E-4 の見込みと行単位の数え方。** AUD_UA4_FREEZE §3 は「B3 −1」を見込んでいた。しかし行単位の数え方（R0）では D.E-4 は B3/B4/B5 の束なので、0 になる（台帳 §12.6 に書かれている。reviewer への確認依頼中と記録されたまま）。
6. **A.P-12 と LEDGER_CROSSCOUNT_DECISION。** この資料（392dc221、FG 88 の時点）は、A.P-12 を含む 9 行を表示の変更で外す案（B）を推奨していない。推奨は A で、binder が消えるか置き換わったときだけ外す。§12.20 は A.P-12 を、Check（`AP12ScanCheck`、独立した binder 0）を根拠に「A.P-22 と同じ扱い」で外した。どの規則で外したかは記録されているが、9 行についての判断は 11-04 の note で reviewer に委ねられたことしか見つからなかった。数の食い違いではない。
7. **FG 75 に入っていないもの（食い違いではなく注意）。** N4-a `LamTelescopeN` の +1（§12.17。入れると 76）は数えていない。D.D-4 の欠陥（§12.22）は、文が今のままでは反駁できるというもので、件数は変えていない。

T1 の値の時刻を照らした結果、FG 台帳の各節に書かれた T1 の値（§12 で 54、§12.1 で 54 のまま、§12.3 / §12.4 で 56、§12.5 で 54、§12.6 で 55、§12.8 以降は 57）は、その節を書いた時刻の T1 台帳の値と合っていた。
