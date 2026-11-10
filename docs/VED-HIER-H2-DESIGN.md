# VED 階層 H2 設計: register を持つ子と親の register（sparkle-ved-hier2）

これは設計文書であり実装ではない。`Sparkle/` と `Tools/` は変更していない。
基準: ved/hier-h1 2a8ff165（PR #157、H1 実装）。前提文書: docs/VED-HIER-DESIGN-v1.md（§7 裁定、§8 実装）。
H2 の裁定 §7.5: 「状態は instance path ごとに独立。同時更新・初期値・reset=0/clock 範囲を別途定義」。
本文書は 327 行への対応、strict 完成、release を主張しない。件数も約束しない。

## 0. 要約（判断の骨子）
- 状態は `HSt := Path → String → Nat`（Path = instance 名の列、鍵は (path, register 名)）。H2 初回は深さ 1（path = `[iname]`）。
- 1 cycle = (a) 現在の状態に対する組合せ評価（親の assign と子の出力）、(b) その cycle の値から全 register（親と全子）を同時更新。
- 初期値は各 module 自身の register init。reset=0、単一 clock は U1 と同じ。子の clock/reset 接続が親の clk/rst の `ref` でなければ拒否。
- 親の証明は子の register を一切見ない。親が使うのは各 instance の出力 stream だけで、それは子の `OutputsStmt` から供給する。子の状態は「射影補題」の中に閉じる。
- 推奨: `U1HStmt` の形は変えず、`runH` を状態付きに一般化する（H1 は「子に register なし」の特殊例として補題で残す）。
- 最初の実測: 子が register を持つ最小例は `#ved_u1_hier` が `[hier-shape]` で拒否する（§6）。この枝では子 module 単体の `#ved_u1` も register 付きのループ形は `[proof]` で拒否する。H2 の子供給は PR #160（`#ved_u1_deep`）に依存する。

## 1. 意味論の拡張

### 1.1 状態: instance path ごとに独立
```
abbrev Path := List String          -- instance 名の列。top = []、子 = [iname]
abbrev HSt  := Path → String → Nat  -- 鍵 (path, register 名)
```
- 鍵は instance 名（`Stmt.inst _ iname _` の第 2 引数）。HierShape の `instNames m.body` Nodup（H1 から既存）により path は一意。
- 同じ子 module の 2 instance は別 path なので別状態になる。register 名は子 module 内の名前で、module をまたいで衝突する。実測（§6 の probe2）では `accMod` の 2 instance が、どちらも register `_tmp_loop_body_2` を持つ。したがって鍵は register 名単独ではなく (path, 名前) でなければならない。「module 単位の状態」は誤りで、拒否対象の対照にする（§7）。
- 配列表現は関数型 `Path → String → Nat` を推奨する。深さ 2 以降でも定義を変えずに済み、H1 の `applyNexts` と同じ形で扱える。（reviewer 質問 Q1）
- 深さ 1 の初回では、使う path は `[]` と `[iname]`（子の宣言 inst）だけ。それ以外の path の値は読まれない（読む箇所を作らない）。

### 1.2 1 cycle
```
stepHS d arr m (inp : Env) (st : HSt) : Option (Env × (HSt → HSt))   -- 概念
  (a) envF   ← evalAssignsI (declWidth m) (instEvalS d st) (arr m) (seed inp st[])
  (b) nextsP ← regNexts (declWidth m) _ (arr m) envF                      -- 親の register
      nextsI ← 各 inst (mn, i, cs) について
                 seedC ← childSeedS c cs envF st[i]
                 envC  ← evalAssigns (declWidth c) (arr c) seedC            -- 子の組合せ
                 regNexts (declWidth c) _ (arr c) envC                      -- 子の register
      st'    := applyH st (([], nextsP) :: nextsI)      -- 同時: 全 nexts は (a) の値のみから計算し、適用は最後
```
- 同時更新: 親・子の register の next 値はすべて同じ cycle の `envF`／`envC` から計算し、適用はその後に 1 回だけ。ある register の新値は同じ cycle の他の register の新値を読まない。
- `instEvalS`: H1 の `instEval` と同じ形で、子の seed に (i) conns の入力 port 値（H1 と同じ）、(ii) 子の register 出力名の現在値 `st [i] r` を追加する。それ以外の名前は H1 と同じく 0 で、WO と undriven 拒否で読まれないことを保証する（0 を値の代用にしない: §1.5）。
- 子の next 値 (b) は instance の位置で評価した値ではなく、確定した `envF` から seed を再構成して再評価する。WOH の `Good`（確定値は instance の読む名前上で評価時の値に一致: `cell_agree`）により、(a) で使った seed と一致する。これは補題 `childNext_agree` として証明する（§2.4 の補題 L3）。代案: `InstEval` が書込みと一緒に子の next 値を返す。順序不変性の定理（`evalAssignsI_perm`、`IELaws`）を再証明する必要があるため、再評価方式を推奨する。（Q2）
- レジスタ出力は同じ cycle で読め、その next は次の cycle に書かれる。これは U1 の `runModule`/`stepModule` と同じ規約で、そのまま引き継ぐ。H1 の `WOH` は `.register` の rd/wr を `[]` とする（`rdH`/`wrH` の `_ => []`）。出力名は seed（状態）から来て、入力式の読みは (b) の `regNexts` が `envF` に対して行う。

### 1.3 初期値・reset・clock
- 初期値 `st0H d m : HSt`: path `[]` は `regsOf m.body`、path `[i]` は `findMod d mn` で解決した子の `regsOf c.body` の init を `encodeInit init (declWidth · n)` で符号化する。契約 `c` を参照しない（返却 `(m, d)` だけから定義）。親の部分は既存の `st0 c m` に一致する（`ShapeCore` の `inits` 条項から導く補題 `st0H_own`）。
- reset: `regNexts` は `env rstName ≠ 0` なら init を使う、既存の一般定義をそのまま使う。reset=0 は意味論の切り捨てではなく文の範囲（`InputsOk`: `ins t kr.2 = 0`）。子の reset port の値は conns 経由で親の reset 値になり 0。reset kind（sync/async）は既存の注記どおり無視する。
- clock は単一。U1 同様、clock の値は意味論に現れない（1 step = 1 cycle）。拒否する条件（`HierShape` に追加）:
  - 子の register の clock 名が、子の `clkRst`（子契約から読んだ clock port 名）と一致しない。
  - 子の clock port の conns が、親の clock の `ref` でない（定数、他の信号、導出式、gated clock を含む）。
  - 子の reset port の conns が、親の reset の `ref` でない。
  - 子が clock/reset port を持たないのに register を持つ。
  - 親が register なしでも、子が register を持つなら親の `clkRst` は `some`（実測: 親 `parTwo` は register を持たなくても `clk`/`rst` を入力に持ち、子へ `ref "clk"`/`ref "rst"` で接続する）。H1 の `c.clkRst = none` 条項は「親も全子も register なし」のときだけ残す。
  - 親と子で register の clock 名・reset 名が違う（別 clock、別 reset）: すべて拒否。複数 clock は H2 範囲外。
- 実測（probe2）の子 module の port は `[_gen_x, clk, rst]`、出力 `out`。

### 1.4 失敗はすべて `none`（0 値で補わない）
H1 の失敗に加え、H2 で追加:
- H1 から引き継ぐ: 子の欠落、primitive の子、入力 port の接続欠落、子に無い port への接続、出力接続が `ref` でない、memory（親・子とも）、燃料切れ。
- 追加: 子の instance（深さ 2 以上。深さ 1 では子の body に `.inst` があれば `none`、H1 の `combOnly` 再帰を深さ 1 では使わない）。
- 追加: 子の register 名が重複する、register 出力名が assign の左辺や入力名と衝突する（§4）。
- 追加: 子の clk/rst conns が §1.3 に反する（意味論側でも `none`。shape だけの拒否にしない）。
- 状態の読み出しは `st [i] r`（全域関数）だが、読むのは `regsOf c.body` の名前だけ。そうでない名前を読む経路は seed 構成に作らない。補題 `seed_regs_only` で「seed が状態から取る名前の集合 = 子の register 出力名」を証明する。

### 1.5 元の宣言から独立
定義は `(d, m, arr)` と入力 stream だけ（`HSt`、`st0H`、`stepHS`、`runHS`）。契約 `c`、宣言 `f`、`Contract.inits` は意味論の定義に出ない。契約が現れるのは文（`InputsOk`、`srcOf`）だけ。子の clock/reset の検査は子 module の `regsOf`（clock 名、reset 名）と conns から行い、子契約は使わない。

### 1.6 葉の補題
- 葉: instance なし（`d.modules = []`、memory なし、`leafBody`）の top では `stepHS d arr m inp st` の `(envF, nexts)` が既存の `stepModule (declWidth m) (arr m) inp` に一致し、`runHS` が `runModule (declWidth m) (arr m) seed K st0 (fun _ _ => 0)` に一致する（path `[]` への制限）。`evalAssignsI_leaf`（H1）と `regNexts` の同一性から、K に関する帰納法。
- 後方互換: 全子が register なし（`regsOf = []`）なら `runHS = runH`（H1）。H1 の定理は特殊例として残る（補題 `runHS_stateless`）。

## 2. 中間契約と、実際の子定理による供給

### 2.1 親の証明が子に求めるもの
親の証明が各 instance に必要とするのは、入力 stream → 出力値の関係である。形は子の `OutputsStmt cc cm g`（U1 の文そのもの）: 範囲内の任意の入力 stream `ins'` と任意の K について、`runModule (child 単独)` が存在し、各 t < K の出力が `srcOf cc g ins' o t` に等しい。親が必要なのは次の等式列。
```
ChildRel_i : ∀ t < K, (hier 実行の instance i の出力値 at t) = srcOf cc_i g_i (insC_i) o t
```
ここで `insC_i t` は instance i が cycle t に見る入力（conns を評価した値）の stream。H1 は子の関数を 1 cycle の値だけで評価していた（組合せだから）。順序回路では stream 全体が要る。

### 2.2 親の証明の構成（child を oracle にする）
1. 親を open module として扱う。IR の `.inst` は open 意味論では no-op で、instance の出力 wire は seed の自由入力（Semantics.lean:185-198）。この性質を使い、親の宣言から各子呼び出し `g x_i` を let 束縛の部分 signal として抽象化し、`f = F (g x_1) … (g x_n)` の形（beta で `rfl`）に置く。親の open な step 補題（親の register は Deep の slot 不変条件 `st (_nm i) = Cdo.irState … i` を使う）は oracle `o_i := g x_i` を自由入力として持つ。
2. 子の関係: `o_i t = srcOf cc_i g_i (obs ∘ x_i) o t` を、子の `OutputsStmt`（実定理、`<decl>.ved_child.<mod>.ved_u1`）を stream `insC_i := obs ∘ x_i` に適用して得る。`sig_self`（H1 に既存）で signal と obs stream の往復を閉じる。
3. 閉じた run と開いた run の一致: oracle の値を seed に与えた open 実行 = hier 実行（補題 L2）。
4. 時間方向の帰納で、親の不変条件 `R t st` を保つ。`outputsH_of_step`（H1）と同じ形。

最終定理では、すべての中間仮説（`ChildRel_i`、束縛 `findMod d mn = some c`、子定理が `d` から解決した module に結ばれていること、`AdmArr`、`InputsOk`）を供給し、未供給の binder を残さない。子定理は H1 と同じく `decide` で `d` から解決した module に束縛する（別 run・同名 module の証明は代用不可）。

### 2.3 子定理（`runModule` 単独）が階層状態の子のスライスに移る仕組み
子の定理は `runModule (declWidth c) (arr c) seed K (st0 cc cm)` について語る。階層 run のうち path `[i]` のスライスで同じ式になる。これが射影補題。

### 2.4 鍵となる補題（射影補題）
```
theorem runHS_proj :
  HierShapeS d m → AdmArr d m arr → runHS d arr m seed K st = some envs →
  ∀ instance (mn, i, cs) ∈ m.body, ∃ c, findMod d mn = some c ∧
    runModule (declWidth c) (arr c) (seedFwd-of insC_i) K (fun n => st [i] n) (fun _ _ => 0)
      = some (envs.map (childEnvOf i cs))
```
`insC_i` は `envs` から定義する child の入力 stream（`childSeed` 由来）。証明の見取り図（K に関する帰納、st を一般化）:
- L1 (葉と同一): 子の 1 cycle `evalAssigns (arr c) (seedC)`＋`regNexts` は、子が `leafBody`（H2 初回: 子は assign と register のみ）のとき `stepModule` に一致する（`evalAssignsI_leaf`、`regNexts` は同一関数）。
- L2 (open/closed 一致): 親の `evalAssignsI` の結果は、instance の出力を seed に与えた open 実行（`evalAssigns`）と一致する。H1 の `instEval_leaf` の一般化。順序は `WOH` と `evalAssignsI_perm`（H1）で任意の許容配列に対して。
- L3 (再評価の一致): 子の next 値を `envF` から再構成した seed で評価しても、(a) の評価時の seed と一致する。`WOH` の `Good`（H1: `good_of_fold`）から。instance の読む名前は後続の文に書かれない、が使われる点。
- L4 (スライスの独立): `applyH st nexts [i] = applyNexts (st [i]) nexts_i`、`applyH st nexts p = st p`（p が他の path のとき）。path ごとの鍵が分かれていることから `funext` と `find?` の補題で示す。他の instance の更新は st [i] に触れない。
- L5 (時間): `runModule` の seed 添字 `K-1-j` と `runHS` の対応は H1 の `seedFwd_time`（Contract）を使う。
- L6 (入力範囲): 子に渡る値が `InputsOk cc cm insC_i` を満たす（データ入力は `2^declWidth` 未満、reset は 0）。値の範囲の不変条件（env の各値がその幅の範囲内）が新しく要る。親の register の next は `mask` される。子の出力は子自身の定理から範囲内。親の wire の評価結果が幅内であることは `evalExpr` の定義側の補題が必要で、H1 は組合せ 1 cycle で同様の補題を持つ。H2 では状態にも及ぶので、帰納の不変条件に `∀ n, st p n < 2^width` を加える。

### 2.5 hier 実行の存在
文は「実行が存在する」ことも結論に含める（§7.3 の空虚さ防止）。H1 の `exists_arr`／`evalAssignsI_succ` に加え、子の `OutputsStmt` が存在を与える（`runModule … = some envs`）。親の step が成功することは、全 cycle で fold が成功することを不変条件に含めて示す（燃料切れなし: 深さ 1 の fuel は定数）。

## 3. 文: `U1HStmt` の形は変えるか
推奨: 形は変えず、`runH` を状態付き `runHS`（初期状態 `st0H d m`）に置き換える。変更は 3 点だけ。
1. `OutputsOnH` の `runH … (st0 c m)` を `runHS … (st0H d m)` にする。
2. `c.clkRst = none` 条項を、子の register 有無に応じた clock/reset 検査（`HierShapeS` の一部）に置き換える。
3. `HierShape`/`OrderOkH` に register の条項（§4）を追加する。

理由:
- 観測（出力 stream が宣言と一致）は変わらない。状態は内部で、`d` と `m` から定義した `st0H` が文に現れるので、監査者は初期状態の定義を読む。
- 別の文を作ると、`U1HStmt` と `U1HSStmt` の 2 つを監査する。H1 は組合せ子の特殊例として補題で残り、重複しない。
- 型の変更が H1 の凍結に触れる懸念: §7 の通り型は未凍結。H1 の補題群（`evalAssignsI_perm`、`instEval_laws`）はそのまま使える。
- 代案（新しい文 `U2HStmt`）: H1 の PR を一切変えずに済む利点があるが、上の重複の費用がある。（Q3）

## 4. Order/Shape の検査
- `WOH` の扱い: `.register` の rd/wr は `[]`（H1 のまま）。レジスタ出力は seed（状態）から来るので、同じ cycle で読める。入力式の読みは後段 (b)。`OrderOk`（U1）が既に持つ register 条項を、`OrderOkH` に追加する（H1 には無い。register がなかったため）:
  - register 出力名は assign・instance 出力の書込みに現れない（多重 driver）。`(wrsH d b)` との交わりが空。
  - register の入力式の読みを含む全読みは、入力 ∪ register 出力 ∪ `wrsH` に含まれる（undriven 拒否）。
  - `nextKeys` Nodup（同じ register 名を 2 回持たない）。register 出力名は入力名でない。
- 拒否（すべて `none` または shape 拒否で、定理は残らない）:
  - assign/reg/inst をまたぐ多重 driver。同一 module 内。
  - 子の register 名が別 path と衝突: 構成上起きない。状態の鍵が (path, 名前) で、path は instance 名の一意性（HierShape）から一意。別 module の同名 register は別鍵。「衝突しない」ことは `st0H`/`applyH` の定義から `funext` で導く補題 L4 の帰結で、検査は追加しない。同じ module 内の重複は `nextKeys` Nodup で拒否する。
  - instance を通る組合せ循環: `WOH` は instance の読む名前を子の入力 port の conns から、書く名前を出力 port の conns から取る（H1 のまま）。子の出力は子の register 出力から組合せ的に生えることがあり、子の入力→出力の組合せ経路は親の WOH では保守的に「全入力を読む」と扱う（子が入力を register で切っていても同じ cycle の依存として扱う）。これにより偽の拒否はあり得るが、偽の受理はない。精密化は後（Q5）。
  - memory: H2 範囲外。親・子とも `none`（意味論）と shape 拒否。
  - 子の別 clock/別 reset: §1.3。
  - 未使用の子 module、`d` と top の不一致、重複名、conns の過不足・方向・幅: H1 の `HierShape`（維持）。

## 5. 最初の H2 スライスの範囲（提案）
- 深さ 1（path = `[iname]`）。
- 子: `assign` と `register`（1 個以上）のみ、memory/primitive/parameter なし、単一出力（H3 は別）、clock/reset は §1.3 を満たす。子の register 数は PR #160 の multi-register U1 の範囲。子の定理は `#ved_u1_deep` の系統（`Cdo.irState` の slot 不変条件）が供給する。
- 親: register なし（組合せ）から始め、通った後に register を持つ親（既存の multi-register 範囲）へ進む。単一出力。
- 同じ子を 2 回呼ぶ例（per-path の状態を観測できる例）を含める。
- 段階: H2a = 組合せ親＋register 子（1 個、2 instance）、H2b = register 親＋register 子。
- 前提: PR #160 のマージ。この枝には `#ved_u1_deep` がなく、`Signal.loop` 形の register 子は plain `#ved_u1` で `[proof]` 拒否される（§6 probe1）。

## 6. 代表と最初の阻害（設計 probe。測定ではない）

### 6.1 inventory との関係
固定 327 行の一覧（results.tsv）はこの worktree の外にあり、読まなかった。したがって inventory の行番号や該当件数は示さない。次は、木にある宣言から形を判断した結果で、行の対応は reviewer か inventory を持つ側が確認する。
- `Tests/Compiler/MultiInstanceTest.lean` の `mesh2x2`: 親は組合せ、`pe` は register 2 個で構造体出力（aOut/pOut）、4 instance。H2＋H3（複数出力）。H2 単独の代表にはならない。
- `synth_keccakRc`（`keccakRcHW`）、`synth_sha256KMux`（`kMux`）、`synth_aesRcon`（`rconHW`）: 木にある宣言を読む限り、どれも `@[hardware_module]` の組合せ関数（`kLut!`）を `#synthesizeVerilog` するだけで、register を持つ子はない。この種の行は H2 の候補ではない。これらが [order] で拒否される原因は調べていない（H2 の範囲外）。
- `synth_spongeD0`: 親 `keccak256SpongeHW` は register を多数持ち、子 `wKeccakF` は複数出力（`KeccakFOut`）で内部に register を持つ。H2＋H3、規模が大きい。
- 単一出力で register を持つ子を持つ宣言は、inventory 側ではなく既存テストにある: `Tests/Compiler/Issue107LetBoundInstanceDup.lean` の `oneInstance`/`threeInstances`（子 `toggle` は Bool、register 1 個、親は register を持つ。`threeInstances` は同一子 3 instance）、`Tests/Ved/NestedCacheCheck.lean` の `parentMix`（子 `accMod`: 8bit register 1 個、親は register 1 個）。これらは H2 の最小代表の候補（327 には加算しない小例）。

### 6.2 probe（scratch は /build 配下、複製を $KJOB_REPORT_PATH の隣に置いた）
- 手順: `kjob lake build Tools.VedU1HierEntry` の後、`kjob lake env lean <file>` のみ。注: manager PR #80 は未配備で、lake env が他の job の olean を見ている可能性がある。この結果は設計判断のための probe であり、測定ではない。
- 宣言: 子 `accMod x := Signal.loop fun s => Signal.register 0#8 (s + x)`（register 1 個、8bit）。
- probe1（/build/h2probe/Probe.lean、複製 `<report dir>/probe/Probe.lean`）:
  - `#ved_u1_hier H2Probe.parTwo`（親は組合せ、`accMod` を 2 instance）: `VED U1 REFUSED H2Probe.parTwo [hier-shape]: instance _tmp_inst_H2Probe.accMod_0: child H2Probe.accMod is not a combinational leaf (register, memory or instance in its body: H2)`。最初の阻害は H1 の shape 検査（意図どおり）。
  - `#ved_u1_hier H2Probe.parReg`（親が register を持ち子も register）: `[hier-shape]: top statement reg _tmp_loop_body_4 … is not an assignment or an instance (registers or memories at the top are not in H1)`。
  - `#ved_u1 H2Probe.accMod`（子単体、この枝の plain `#ved_u1`）: `[proof]: errors were logged while elaborating the proof; first: unsolved goals … Signal.loop`。この枝の生成器は register を持つ `Signal.loop` 形の単独証明に届かない。PR #160 の `#ved_u1_deep` が対象。H2 は #160 に依存する（§5）。
- probe2（/build/h2probe/Probe2.lean、複製 `<report dir>/probe/Probe2.lean`）: `synthesizeCombinational` が返す `(m, d)` を表示。
  - 親 `parTwo` の body: `inst accMod _tmp_inst_H2Probe.accMod_0 [clk↦ref clk, rst↦ref rst, _gen_x↦ref _gen_a, out↦ref _gen_p]` と `…_1`、`assign _gen_out (sub _gen_p _gen_q)`、`assign out`。親の inputs は `[_gen_a, _gen_b, clk, rst]`（親は register なしでも clk/rst を持つ）。
  - 子 `accMod` の body: `assign _tmp_reg_input_1 = _tmp_loop_0 + _gen_x`、`register _tmp_loop_body_2 clk (rst, sync) ← _tmp_reg_input_1 (init 0)`、`assign _tmp_loop_0 = _tmp_loop_body_2`、`assign out = _tmp_loop_0`。2 instance とも register 名は `_tmp_loop_body_2`（鍵が path を含む必要の実例）。
  - instance 名は `_tmp_inst_H2Probe.accMod_0` のようにドットを含む文字列。path の鍵としては単なる文字列。生成する証明テキストでの綴りは H1 の private 名の扱いと同様に注意が要る。
- 計測値（heartbeat、時間、メモリ）は取っていない（設計 probe）。
- 未確認（実装前に確認する事項）: DeepElab（`#verify_elab_deep`）が `@[hardware_module]` の呼び出しを含む親宣言に対して定数を生成できるか。この枝には multi-register の Deep がなく、確認できなかった。生成できない場合、親の open step 補題（§2.2 の 1）の生成器は別途要る。

## 7. 実装時の対照（すべて拒否、定理は残らない）
H1 の対照（`Tests/Ved/U1HierCheck.lean`）と同じ方式（`checkU1H` を 1 箇所だけ変えた `(m, d)` に走らせ、名前の付いた段で拒否、base の定数が残らないこと）。型レベルの対照は `elabTermEnsuringType` の拒否として書く。
1. 子の register init を変える（`regsOf` の init）: 子の `OutputsStmt` が成立しない／`st0H` が宣言とずれる。
2. 子の next 値（register 入力式）を変える: 子の定理との不一致。
3. 同じ子の 2 instance を、状態が異なる状態で入れ替える（conns か instance 名の入れ替え）: 状態が違うので出力が変わる。2 instance に異なる入力を与えて観測できるようにする。
4. 親の register が間違った instance を読む（`ref` の取り違え）: 出力が変わる。
5. 子の状態を 2 instance で共有する（「module ごとに 1 状態」の実装誤り）: 鍵を (path, 名前) ではなく名前だけにした変異版 `stepHS` で、2 instance の出力が食い違うことを concrete 値で確認し、その変異版では文が成立しない。
6. 別 run の子（別 Design の子 module、同名の別定義）: `d` から解決した module との束縛（`decide`）で拒否。
7. 追加: 子の clk を親の clk 以外に接続、子の rst を定数に接続、子の register 重複名、register 出力への assign（多重 driver）、instance を通る組合せ循環。
- 肯定側: `stepHS` を concrete 値で評価し、宣言の値と比較する。2 instance に異なる入力を与え、状態を 2 cycle 以上進める。小例は 327 に加算しない。

## 8. 費用とリスク
- 証明の大きさ: 親の open step 補題は親 register 数に比例（Deep の slot ごとの `simp`）。子ごとの `OutputsStmt` は子の register 数に比例し、instance 数 × 子の register 数では増えない（同じ子の定理を `d` から解決して再利用する）。ただし射影補題と L2/L3 の適用は instance ごとに 1 回。
- heartbeat: #160 の記録のとおり、複数 register＋複数入力で既定の heartbeat を超える例がある（`[checker]` で拒否、受理はしない）。大域上限は上げない。H2 でこれが親・子それぞれの証明に加算される。
- 分割する補題（slot ごと・instance ごと）:
  - 一般補題（module に依存しない、1 回だけ証明）: L1〜L6、`runHS_proj`、`runHS_stateless`、`st0H_own`、`seed_regs_only`。
  - slot ごと: 親の register の不変条件（Deep の生成）。
  - instance ごと: 子の定理の束縛（`decide`）と `ChildRel_i` の適用（生成テキスト）。
- 主なリスク:
  1. 親の抽象化 `f = F (g x_1) … (g x_n)` の生成（let 束縛の部分 signal の特定）。`kabstract` で子呼び出しを見つけられるか未検証。
  2. DeepElab が hardware_module 呼び出しを含む親を扱えるか（未確認、§6）。
  3. 値の範囲の不変条件（L6）の追加。
  4. instance 名のドットや private 名の、生成する証明テキストでの綴り（H1 で private 親が 1 件出ている）。
  5. 子の組合せ経路の保守的な扱い（§4）による偽の拒否。
- 補題の本数や規模は見積りで、「1 本で済む」とは言わない。

## 9. reviewer への質問
1. 状態の表現: (a) `Path → String → Nat`（推奨、深さ拡張に強い）、(b) 深さ 1 専用の 2 段（親の状態、instance 名→register 名→値）。
2. 子の next 値: (a) `envF` から seed を再構成して再評価（推奨、H1 の順序不変性の定理を再利用）、(b) `InstEval` が書込みと一緒に next 値を返す（定義は素直だが `IELaws`/`evalAssignsI_perm` の再証明）。
3. 文: (a) `U1HStmt` の形を維持して `runHS` に置換（推奨）、(b) 新しい `U2HStmt`。
4. 初回スライス: (a) H2a（組合せ親＋register 子）から（推奨）、(b) 最初から register 親＋register 子。
5. instance を通る組合せ循環の扱い: (a) 子の「全入力→出力」を保守的に依存とみなす（推奨。偽の拒否はあり得る）、(b) 子の入力→出力の組合せ経路を module ごとに解析して精密化（費用大）。
6. 子 clock/reset の検査位置: (a) shape と意味論の両方で `none`（推奨）、(b) shape のみ。
7. 依存: H2 の実装を PR #160（`#ved_u1_deep`）のマージ後に始める（推奨）か、この枝の plain `#ved_u1` を拡張して子の定理を供給するか。
8. 親の抽象化の生成（§8 リスク 1・2）について、実装前に `#verify_elab_deep` と `kabstract` の可否を確認する小さな probe の単位を先に切る（推奨）か、実装単位の中で確認するか。
9. 代表の指定: `parentMix`（NestedCacheCheck）または `threeInstances`（Issue107）を最初の小例とし、inventory 側の行は reviewer が results.tsv から指定する（推奨）。

## 10. 根拠
- 設計: docs/VED-HIER-DESIGN-v1.md §7、§8。
- コード（ved/hier-h1 2a8ff165）: Tools/VedU1HierSem.lean（`stepH`、`runH`、`WOH`、`evalAssignsI_perm`、`IELaws`）、Tools/VedU1HierComp.lean、Tools/VedU1Hier.lean（`HierShape`、`OrderOkH`、`AdmArr`、`OutputsOnH`、`U1HStmt`）、Tools/VedU1Contract.lean（`regsOf`、`st0`、`OrderOk`、`OutputsStmt`、`U1Stmt`）、Sparkle/IR/Semantics.lean（`regNexts`、`applyNexts`、`stepModule`、`runModule`）。
- 別枝: `git show ved/multireg:Tools/VedU1Deep.lean`（PR #160、multi-register U1、slot 不変条件）。
- probe: /build/h2probe/Probe.lean、/build/h2probe/Probe2.lean（複製: `$KJOB_REPORT_PATH` と同じディレクトリの `probe/`）。ログ・測定値はこの木に置かない。
