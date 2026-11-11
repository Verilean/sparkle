# VED 階層 H2 設計: register を持つ子と親の register（sparkle-ved-hier2）

これは設計文書であり実装ではない。`Sparkle/` と `Tools/` は変更していない。
基準: ved/hier-h1 2a8ff165（PR #157、H1 実装）。前提文書: docs/VED-HIER-DESIGN-v1.md（§7 裁定、§8 実装）。
H2 の裁定 §7.5: 「状態は instance path ごとに独立。同時更新・初期値・reset=0/clock 範囲を別途定義」。
本文書は 327 行への対応、strict 完成、release を主張しない。件数も約束しない。
reviewer 裁定（§11、対象 12135944）を §0〜§10 の本文に反映済み。§11 はその対応表で、追記だけの注記ではない。

## 0. 要約（判断の骨子）
- 状態は `HSt := Path → String → Nat`。Path = instance 名の列（root = `[]`）。同じ module の複数 instance は別 path で区別する。読み書きするのは解決済みの実 register だけ。H2 初回は深さ 1（path = `[iname]`）。
- 1 cycle = (a) 更新前の状態に対する組合せ評価、(b) 全 register（親と全子）の next 値をすべて更新前状態の cycle 値から作り、(c) 最後に 1 回だけ同時更新する。
- 初期値は各 module 自身の register init。reset=0（文の範囲）。子の clock/reset 接続の検査は、子 module と conns だけから定義し、契約を参照しない（§1.3）。
- 親の証明は子の register を直接は見ない。親が使うのは各 instance の出力 stream で、子の `OutputsStmt` から供給する。子の状態は射影補題の中に閉じる。射影補題は子の全 Env の等式ではなく、存在量化した子 trace と port・状態の対応で述べる（§2.4）。
- 文は新しい定義 `U2HStmt` / `runHS`。既存の `U1HStmt` / `runH` は置換しない。H1 の保証・CI・測定は固定のまま。H1 の条件下で `runHS_stateless` と葉の `runModule` との対応を先に証明し、統一はその後に検討する（§3）。
- 最初の実測: 子が register を持つ最小例は `#ved_u1_hier` が `[hier-shape]` で拒否する（§6）。子 module 単体の `#ved_u1` も register 付きのループ形は `[proof]` で拒否する。`Tools/VedU1Deep.lean`（`#ved_u1_deep`）は base にも存在する。未統合なのは PR #160 の multi-register/Bool 拡張である。H2 の子供給はこの #160 の生成器を再利用する（plain U1 の別拡張はしない）。
- H2 の実装、文の凍結、strict 件数は承認されていない（§12）。

## 1. 意味論の拡張

### 1.1 状態: instance path ごとに独立
```
abbrev Path := List String          -- instance 名の列。root = []、深さ 1 の子 = [iname]
abbrev HSt  := Path → String → Nat  -- 鍵 (path, register 名)
```
- 鍵は instance 名（`Stmt.inst _ iname _` の第 2 引数）。HierShape の `instNames m.body` Nodup（H1 から既存）により、同じ module 内の path は一意。
- 同じ子 module の 2 instance は別 path なので別状態になる。register 名は子 module 内の名前で、module をまたいで衝突する。実測（§6 の probe2）では `accMod` の 2 instance が、どちらも register `_tmp_loop_body_2` を持つ。したがって鍵は register 名単独ではなく (path, 名前) でなければならない。「module 単位の状態」は誤りで、拒否対象の対照にする（§7）。
- 関数型 `Path → String → Nat`（Q1 (a)）は深さ 2 以降でも定義を変えずに済み、H1 の `applyNexts` と同じ形で扱える。
- 「実 register だけを読み書きする」: 状態を読む箇所は、解決済みの module（`findMod` が返した module）の `regsOf` が列挙する名前に限る。それ以外の (path, 名前) は st に値があっても読まれず、書かれもしない。`seed_regs_only`（§1.4）で証明する。
- 深さ 1 の初回で使う path は `[]` と `[iname]`（子の宣言 inst）だけ。

### 1.2 1 cycle: 全 next は更新前状態から作り、最後に同時更新
```
stepHS d arr m (inp : Env) (st : HSt) : Option (Env × HSt)   -- 概念
  (a) envF   ← evalAssignsI (declWidth m) (instEvalS d st) (arr m) (seed inp st[])   -- st は更新前
  (b) nextsP ← regNexts (declWidth m) _ (arr m) envF                                  -- 親の register
      nextsI ← 各 inst (mn, i, cs) について
                 seedC ← childSeedS c cs envF st[i]                                 -- st は更新前
                 envC  ← evalAssigns (declWidth c) (arr c) seedC
                 regNexts (declWidth c) _ (arr c) envC
  (c) st'    := applyH st (([], nextsP) :: nextsI)     -- 適用は最後に 1 回だけ
```
- 同時更新: (a)(b) のどこでも `st'` を読まない。親・子の register の next 値は、すべて同じ `st` と同じ cycle の `envF`／`envC` から計算する。ある register の新値は、同じ cycle の他の register の新値を読まない。`applyH` は互いに異なる (path, 名前) への書込みなので、適用順に依存しない（L4）。
- `instEvalS`: H1 の `instEval` と同じ形で、子の seed に (i) conns の入力 port 値（H1 と同じ）、(ii) 子の register 出力名の現在値 `st [i] r` を追加する。それ以外の名前は H1 と同じく 0 で、WO と undriven 拒否で読まれないことを保証する（0 を値の代用にしない: §1.5）。
- 子の next 値は、確定した `envF` から seed を再構成して再評価する（Q2 (a)、最初の実装方式）。`InstEval` が書込みと一緒に next 値を返す方式は、`IELaws`/`evalAssignsI_perm` の再証明が要るため採らない。再評価方式の正しさは補題 `childNext_agree` で担保する。この補題は次の 3 つの一致に分け、状態を固定した `IELaws`/`Good` から証明する（`st` を固定し、評価順の任意性は `evalAssignsI_perm` が与える）:
  1. 入力の一致: 再構成した seed の入力 port 値 = (a) で instance 位置に評価時に渡した値（`cell_agree`: 確定値は instance の読む名前上で評価時の値に一致）。
  2. 出力の一致: 子の組合せ評価 `envC` の出力 port 値 = (a) で親の env に書かれた instance 出力値（H1 の `instEval_leaf` の一般化。子の register 出力は `st [i]` から seed に入るので、同じ `st` なら同じ値）。
  3. 次状態の一致: `regNexts … envC` が、同じ seed から子単体の `stepModule` が与える next と一致する（L1）。
  3 つを別々の補題にするのは、出力が合っても next が合う保証にならない（再評価の seed が評価時と違えば register 入力式の値が変わる）ため。
- レジスタ出力は同じ cycle で読め、その next は次の cycle に書かれる。これは U1 の `runModule`/`stepModule` と同じ規約。H1 の `WOH` は `.register` の rd/wr を `[]` とする（`rdH`/`wrH` の `_ => []`）。出力名は seed（状態）から来て、入力式の読みは (b) の `regNexts` が `envF` に対して行う。

### 1.3 初期値・reset・clock
- 初期値 `st0H d m : HSt`: path `[]` は `regsOf m.body`、path `[i]` は `findMod d mn` で解決した子の `regsOf c.body` の init を `encodeInit init (declWidth · n)` で符号化する。契約 `c` を参照しない（返却 `(m, d)` だけから定義）。親の部分は既存の `st0 c m` に一致する（補題 `st0H_own`、`ShapeCore` の `inits` 条項から導く）。初期値の一致（子の `st0 cc cm` と `st0H` の path `[i]` のスライス）は、射影補題の中ではなく独立の補題 `st0H_slice` として証明し、射影補題の初期条件に供給する（§2.4）。
- reset: `regNexts` は `env rstName ≠ 0` なら init を使う、既存の一般定義をそのまま使う。reset=0 は意味論の切り捨てではなく文の範囲（`InputsOk`: `ins t kr.2 = 0`）。reset kind（sync/async）は既存の注記どおり無視する。
- clock の扱いは次の 2 つを分けて述べる（P2-1）:
  1. register の更新は clock の edge を検査しない。1 step = 1 cycle で、`regNexts` は clock 入力の値を見ない。
  2. ただし clock 入力は env 上の普通の入力名であり、`Expr.ref` がそれを読むことはあり得る。「clock の値は意味論に現れない」とは言わない。読んだ場合の値は入力 stream の値そのもの。
  - `InputsOk` の clock と reset に関する量化は変えない: clock は全称（任意の値）、reset = 0。`clock = 0` への固定や、clock に関する幅条件の追加で狭めない。H2 の定理は、clock が任意の値を取る stream すべてについて成り立つ（子の clock port への conns が `ref clk` なら、子が `ref` で読む clock 値も同じ値になる）。
- 子の clock/reset の検査（`HierShapeS` と `stepHS` の両方に置く。Q6 (a)）。判定は子 module（`regsOf` の clock 名・reset 名、`inputs`）と親の conns だけから定義する。子契約は参照しない（旧版は子契約から clock port 名を読んでいたが、§1.5 の「artifact だけ」と矛盾するので改める）。判定の述語を `clkRstOk d m` とする:
  - 子の register が 1 つ以上あるとき、全 register の clock 名が同一（`kc`）、reset 名が同一（`kr`）で、`kc`・`kr` は子の入力 port 名。
  - 子の `kc` port への conns が、親の clock 入力（親の register の clock 名、親が register を持たなければ親の入力のうち `kc` に接続された `ref` の名前の 1 つ）の `ref`。`kr` port への conns が、親の reset 入力の `ref`。定数、他の信号、導出式、gated clock への接続は拒否。
  - 子が register を持たないなら、clock/reset port の conns は H1 の通常の入力 port の扱い（拒否条件を追加しない）。
  - 子が register を持つのに `kc`/`kr` に当たる入力 port が無い場合は拒否。
  - 親が register なしでも、子が register を持つなら親は clock/reset 入力を持つ必要がある（実測: 親 `parTwo` は register を持たなくても `clk`/`rst` を入力に持ち、子へ `ref "clk"`/`ref "rst"` で接続する）。H1 の `c.clkRst = none` 条項は「親も全子も register なし」のときだけ残す。この条項が参照する `c.clkRst` は文の側の条件であり、意味論の `clkRstOk` は契約を参照しない。
  - 複数 clock、別 reset は H2 範囲外で拒否する。
- 親子で clock/reset のローカル名が異なること（例: 親 `clk`、子 `clock`）と、別 clock への接続は区別する。前者は conns が親の clock 入力の `ref` ならよい（名前は port 名と信号名で違ってよい）。後者（親の別の入力、導出信号への接続）は拒否する。初回スライスで「親子で名前が同じ場合だけ」に制限する選択をするなら、それは別 clock を扱えないことではなく、被覆の制限にすぎない。制限しても、受理された定理の意味は変わらない（拒否が増えるだけ）。
- 実測（probe2）の子 module の port は `[_gen_x, clk, rst]`、出力 `out`。

### 1.4 失敗はすべて `none`（0 値で補わない）
H1 の失敗に加え、H2 で追加:
- H1 から引き継ぐ: 子の欠落、primitive の子、入力 port の接続欠落、子に無い port への接続、出力接続が `ref` でない、memory（親・子とも）、燃料切れ。
- 追加: 子の instance（深さ 2 以上。深さ 1 では子の body に `.inst` があれば `none`、H1 の `combOnly` 再帰を深さ 1 では使わない）。
- 追加: 子の register 名が重複する、register 出力名が assign の左辺や入力名と衝突する（§4）。
- 追加: `clkRstOk` が偽（§1.3）。意味論側でも `none`。shape だけの拒否にしない。
- 状態の読み出しは `st [i] r`（全域関数）だが、読むのは `regsOf c.body` の名前だけ。補題 `seed_regs_only` で「seed が状態から取る名前の集合 = 解決済みの子の register 出力名」を証明する。

### 1.5 元の宣言から独立
定義は `(d, m, arr)` と入力 stream だけ（`HSt`、`st0H`、`stepHS`、`runHS`、`clkRstOk`）。契約 `c`、宣言 `f`、`Contract.inits` は意味論の定義に出ない。契約が現れるのは文（`InputsOk`、`srcOf`）だけ。§1.3 の clock/reset の検査は子 module の `regsOf` と conns から行い、子契約は使わない。

### 1.6 葉の補題と `runHS_stateless`
- 葉: instance なし（`d.modules = []`、memory なし、`leafBody`）の top では `stepHS d arr m inp st` の `(envF, nexts)` が既存の `stepModule (declWidth m) (arr m) inp` に一致し、`runHS` が `runModule (declWidth m) (arr m) seed K st0 (fun _ _ => 0)` に一致する（path `[]` への制限）。`evalAssignsI_leaf`（H1）と `regNexts` の同一性から、K に関する帰納法。
- `runHS_stateless`（Q3 (b)）: H1 の条件（全子が register なし、親も register なし）の下で、`runHS` は H1 の `runH` と同じ envs を返す。この補題と上の葉の対応が先に証明すべきもの。これが通るまで `U1HStmt`/`runH` との統一は検討しない。
- `runH` は変更しない。H1 の実装・CI・測定は固定のまま。

## 2. 中間契約と、実際の子定理による供給

### 2.1 親の証明が子に求めるもの
親の証明が各 instance に必要とするのは、入力 stream → 出力値の関係である。形は子の `OutputsStmt cc cm g`（U1 の文そのもの）: 範囲内の任意の入力 stream `ins'` と任意の K について、`runModule (child 単独)` が存在し、各 t < K の出力が `srcOf cc g ins' o t` に等しい。親が必要なのは次の等式列。
```
ChildRel_i : ∀ t < K, (hier 実行の instance i の出力値 at t) = srcOf cc_i g_i (obs ∘ x_i) o t
```
ここで `x_i` は親の宣言が instance i に与えると期待する入力 signal、`obs ∘ x_i` はその観測 stream。H1 は子の関数を 1 cycle の値だけで評価していた（組合せだから）。順序回路では stream 全体が要る。

次の 2 つは別の事実であり、混ぜない:
- (F1) 子定理: `OutputsStmt` は「初期状態 `st0 cc cm` から出発した `runModule`」についての文。範囲内の任意の入力 stream に対する出力の等式を与える。
- (F2) 入力一致: 親の宣言が期待する入力 signal の stream `obs ∘ x_i` と、hier 実行の conns を評価した実 stream `insC_i` が、t < K で一致すること。これは親側の補題（親の open な step 補題の不変条件、§2.2）から供給する。子定理からは出ない。

### 2.2 親の証明の構成（child を oracle にする）
1. 親を open module として扱う。IR の `.inst` は open 意味論では no-op で、instance の出力 wire は seed の自由入力（Semantics.lean:185-198）。この性質を使い、親の宣言から各子呼び出し `g x_i` を let 束縛の部分 signal として抽象化し、`f = F (g x_1) … (g x_n)` の形（beta で `rfl`）に置く。親の open な step 補題（親の register は Deep の slot 不変条件 `st (_nm i) = Cdo.irState … i` を使う）は oracle `o_i := g x_i` を自由入力として持つ。
   - この抽象化は `kabstract` の成功だけでは根拠にならない。open 親の宣言と元の親宣言が等しいことをカーネルが検査する等式（`F (g x_1) … (g x_n) = f`）として結ぶ（§12 の単位 1）。
2. 子の関係: `o_i t = srcOf cc_i g_i (obs ∘ x_i) o t` を、子の `OutputsStmt`（実定理、`<decl>.ved_child.<mod>.ved_u1`）を stream `obs ∘ x_i` に適用して得る。`sig_self`（H1 に既存）で signal と obs stream の往復を閉じる。
3. 閉じた run と開いた run の一致: oracle の値を seed に与えた open 実行 = hier 実行（補題 L2）。
4. 時間方向の帰納で、親の不変条件 `R t st` を保つ。`outputsH_of_step`（H1）と同じ形。

最終定理では、すべての中間仮説（`ChildRel_i`、束縛 `findMod d mn = some c`、子定理が `d` から解決した module に結ばれていること、`AdmArr`、`InputsOk`、(F2)）を供給し、未供給の binder を残さない。子定理は H1 と同じく `decide` で `d` から解決した module に束縛する。別 run・同名 module の証明は、返却 artifact の値が同じで定理が正しいならそのまま使える（値の同一性は `decide` が検査する）。使えないのは、同名で値が違う module の証明と、`d` に結ばれていない証明である。

### 2.3 子定理が階層状態の子のスライスに移る仕組み
子の定理は `runModule (declWidth c) (arr c) seed K (st0 cc cm)` について語る。階層 run のうち path `[i]` のスライスで同じ式になる。これが射影補題。ただし、スライスから復元できるのは、親の Env と conns で決まる範囲（出力 port、入力 port、register 状態）だけ。子の全内部 Env は復元できない（§2.4）。

### 2.4 射影補題（P1-1 の修正後）
旧版は右辺を `envs.map (childEnvOf i cs)`（親の Env だけから子の全内部 Env を再構成）としていたが、子に出力へ届かない register や内部 wire があると、その値は親の trace から決まらないので、一般には成り立たない。conns から子の全 Env の等式を主張しない。次の形にする:
```
theorem runHS_proj :
  HierShapeS d m → AdmArr d m arr →
  runHSTrace d arr m inp K = some (envs, sts) →          -- sts : List HSt、cycle 毎の更新前状態
  ∀ instance (mn, i, cs) ∈ m.body, ∃ c cenvs,
    findMod d mn = some c ∧
    runModule (declWidth c) (arr c) (seedFwd insC_i) K (st0Of c) (fun _ _ => 0) = some cenvs ∧
    (∀ t < K,                                             -- 3 種の対応を別々に
       (入力 port)   ∀ p ∈ inPorts c, (cenvs[t]) p = evalExpr (conn cs p) envs[t]
     ∧ (出力 port)   ∀ q ∈ outPorts c, envs[t] (outRef cs q) = (cenvs[t]) q
     ∧ (状態)        ∀ r ∈ regsOf c.body, sts[t] [i] r = childRegAt cenvs t r)
```
- `insC_i` は入力 port の conns を `envs` で評価した stream。`childRegAt` は子の run の cycle t の register 値（`runModule` の状態履歴を返す補助定義 `runModuleTrace` を、`runModule` と同じ反復として定義し、一致の補題を付ける）。この補助データが子の cycle trace / 状態履歴を保持する役割を持つ。
- 右辺は存在量化した子 trace `cenvs`。出力 port・入力 port・register 状態の 3 つの対応だけを述べ、`cenvs` の他の（出力に届かない）内部 wire や register の値については何も言わない。
- 初期値の一致 `st0Of c = (st0H d m) [i]` のスライス（`runModule` に渡す初期状態が階層の初期状態の path `[i]` に一致）は補題 `st0H_slice`（§1.3）で別に供給する。射影補題の内部で初期値を導かない。
- 親の宣言が期待する入力 signal `x_i` と実 stream `insC_i` の一致は含まない（(F2)、§2.1）。
- 証明の部品（K に関する帰納、st を一般化）:
  - L1 (葉と同一): 子の 1 cycle `evalAssigns (arr c) (seedC)`＋`regNexts` は、子が `leafBody`（H2 初回: 子は assign と register のみ）のとき `stepModule` に一致する（`evalAssignsI_leaf`、`regNexts` は同一関数）。
  - L2 (open/closed 一致): 親の `evalAssignsI` の結果は、instance の出力を seed に与えた open 実行（`evalAssigns`）と一致する。H1 の `instEval_leaf` の一般化。順序は `WOH` と `evalAssignsI_perm`（H1）で任意の許容配列に対して。
  - L3 (再評価の一致): `childNext_agree`（§1.2 の 3 つの一致）。
  - L4 (スライスの独立): `applyH st nexts [i] = applyNexts (st [i]) nexts_i`、`applyH st nexts p = st p`（p が他の path のとき）。path ごとの鍵が分かれていることから `funext` と `find?` の補題で示す。他の instance の更新は st [i] に触れない。
  - L5 (時間): `runModule` の seed 添字 `K-1-j` と `runHS` の対応は H1 の `seedFwd_time`（Contract）を使う。
  - L6 (入力範囲): 子に渡る値が `InputsOk cc cm insC_i` を満たす（データ入力は `2^declWidth` 未満、reset は 0）。値の範囲の不変条件（env の各値がその幅の範囲内）が新しく要る。親の register の next は `mask` される。子の出力は子自身の定理から範囲内。親の wire の評価結果が幅内であることは `evalExpr` の定義側の補題が必要。H2 では状態にも及ぶので、帰納の不変条件に `∀ n, st p n < 2^width` を加える。clock は `InputsOk` の全称のままで、範囲の仮定を追加しない。

### 2.5 証明順: hier run の存在と射影の循環を避ける（P1-2）
旧版は、射影補題が「成功した hier run」を前提とし、§2.5 が hier run の存在を子の `OutputsStmt` から得るとしていた。未知の `envs` から `insC_i` を定義して存在を再び得ると循環する。さらに `OutputsStmt` は初期状態からの run の性質であり、任意の `st` からの 1 step の成功を直接は与えない。そこで、次の順に証明する。

不変条件 `Inv t`（t cycle 進んだ時点、入力 stream の prefix `inp[0..t)` に対して）:
- (I1) hier run の t cycle が成功し、更新後の状態が `st_t`。
- (I2) 各 instance i について、子の入力履歴 `insC_i[0..t)`（I1 の `envs[0..t)` を conns で評価したもの）を入力とする子の `runModule` が初期状態 `st0Of c` から t cycle 成功し、その最終状態が `st_t [i]` と一致する（register 状態の対応のみ。他の内部値は言わない）。
- (I3) 範囲の不変条件（L6）。

帰納の step（cycle t → t+1）:
1. 親の `WOH` の fold 順（`evalAssignsI` が実際に評価する順）で `envF` を作る。instance i に到達した時点で、その入力 port conns の読む名前は、すべてそれ以前に書かれ確定している（`WOH` の保証）。したがって `insC_i[t]` はこの時点で決まる。これで子の入力履歴を `insC_i[0..t+1)` に延長する。
2. 子の 1 step の成功は、子の `OrderOk`/`AdmArr`（子の shape）から任意の状態・範囲内の seed に対して示す（`exists_arr` の子版）。`OutputsStmt` からは取らない。`OutputsStmt` から取るのは出力値の等式（`ChildRel_i`）だけである。
3. (I2) の延長: 子の run が prefix `insC_i[0..t)` で `st_t [i]` に至っているので、その 1 step は `runModule` の t+1 cycle の 1 step と一致する（L1・L4）。
4. 親の step 全体の成功は、fold の各段の成功（instance 段は 2 から）と `regNexts`（成功は `AdmArr` から）。(I1) が従う。
5. 結論の存在（文が主張する「実行が存在する」）は、K までの帰納の結果として得る。`OutputsStmt` を使う箇所（`ChildRel_i`）は帰納の外で、確定した run に対して行う。

有限 prefix と stream:
- `OutputsStmt` は全域の stream `ins'` を量化する。`ChildRel_i` に使う `ins'` は子の入力 stream `obs ∘ x_i`（宣言側の全域 stream）にとる。これは親の宣言の信号なので、有限 prefix を stream に延長する必要がない。ただし、`obs ∘ x_i` が `InputsOk` の範囲内であることは、t ≥ K も含めて親の宣言側の不変条件から示す（L6 の宣言側版）。
- 実 stream `insC_i`（t < K のみ定義）と `obs ∘ x_i` は (F2) で t < K について一致し、`runModule` は K cycle のうち t < K の seed しか読まないので、prefix 一致の補題 `runModule_prefix`（seed が t < K で一致すれば結果が一致）で結ぶ。
- 実 stream を 0 などで stream に延長する経路を選ぶ場合は、`srcOf` の因果性（出力 t が入力 t' ≤ t だけに依存する）の補題を別に明記して証明する。本設計はこの経路を採らない。

## 3. 文: 別定義 `U2HStmt` / `runHS`（Q3 (b)）
`U1HStmt` の形は変えず新しい定義を並べる。
1. `U2HStmt` は `U1HStmt` と同じ形で、`OutputsOnH` の `runH … (st0 c m)` を `runHS … (st0H d m)` にしたもの（`OutputsOnHS`）。
2. `c.clkRst = none` 条項を `clkRstOk`（§1.3）に置き換える。
3. `HierShape`/`OrderOkH` に register の条項（§4）を足した `HierShapeS`/`OrderOkHS` を使う。
- 既存の `U1HStmt` / `runH` は置換も変更もしない。H1 の保証・CI・測定は固定。
- 順序: (i) `runHS_stateless`（H1 条件下で `runHS = runH`）と葉の `runModule` との対応、(ii) その上に H2 の補題、(iii) 統一（`U1HStmt` を `U2HStmt` に置換するか、並存させるか）は (i) の後に別途検討する。
- 理由: H1 の凍結に触れず、監査者は 2 つの文を比べられる。観測（出力 stream が宣言と一致）は同じ。状態は内部で、`d` と `m` から定義した `st0H` が文に現れる。

## 4. Order/Shape の検査
- `WOH` の扱い: `.register` の rd/wr は `[]`（H1 のまま）。レジスタ出力は seed（状態）から来るので、同じ cycle で読める。入力式の読みは後段 (b)。`OrderOk`（U1）が既に持つ register 条項を、`OrderOkHS` に追加する（H1 には無い。register がなかったため）:
  - register 出力名は assign・instance 出力の書込みに現れない（多重 driver）。`(wrsH d b)` との交わりが空。
  - register の入力式の読みを含む全読みは、入力 ∪ register 出力 ∪ `wrsH` に含まれる（undriven 拒否）。
  - `nextKeys` Nodup（同じ register 名を 2 回持たない）。register 出力名は入力名でない。
- 拒否（すべて `none` または shape 拒否で、定理は残らない）:
  - assign/reg/inst をまたぐ多重 driver。同一 module 内。
  - 子の register 名が別 path と衝突: 構成上起きない。状態の鍵が (path, 名前) で、path は instance 名の一意性（HierShape）から一意。別 module の同名 register は別鍵。「衝突しない」ことは `st0H`/`applyH` の定義から `funext` で導く補題 L4 の帰結で、検査は追加しない。同じ module 内の重複は `nextKeys` Nodup で拒否する。
  - instance を通る組合せ循環（Q5 (a)、保守的）: `WOH` は instance の読む名前を子の入力 port の conns から、書く名前を出力 port の conns から取る（H1 のまま）。子の各出力は、その子の全入力に組合せ的に依存するとみなす。子が入力を register で切っていて、同じ cycle の組合せ依存が実際には無くても、同じ cycle の依存として扱う。これにより、順序回路として合法な回路を拒否することがある（偽の拒否）。偽の受理はない。子の入力→出力の組合せ経路を module ごとに解析する精密化は後続の仕事で、H2 の初回には入れない。
  - memory: H2 範囲外。親・子とも `none`（意味論）と shape 拒否。
  - `clkRstOk` が偽（§1.3）: shape と意味論の両方で拒否（Q6 (a)）。
  - 未使用の子 module、`d` と top の不一致、重複名、conns の過不足・方向・幅: H1 の `HierShape`（維持）。

## 5. 最初の H2 スライスの範囲
- 深さ 1（path = `[iname]`）。
- 子: `assign` と `register`（1 個以上）のみ、memory/primitive/parameter なし、単一出力（H3 は別）、`clkRstOk` を満たす。子の定理は PR #160 の `#ved_u1_deep` 系統（multi-register/Bool、`Cdo.irState` の slot 不変条件）の生成器を再利用して供給する。plain U1 の別拡張は作らない（Q7）。
- 段階（Q4 (a)）:
  - H2a: register なしの親、同じ register 子の 2 instance（最小例は `parTwo` 相当）。最初の例は 2 instance に異なる入力を与え、出力を非対称にして（例: `out = p - q`）、状態が共有されたら観測できるようにする。
  - H2b: register を持つ親＋register 子（`parentMix`: `Tests/Ved/NestedCacheCheck.lean`）。
  - 次の回帰: `threeInstances`（`Tests/Compiler/Issue107LetBoundInstanceDup.lean`、同一子 3 instance）。
- 依存（Q7）: 子の定理の供給は #160 の生成器に依存する。統合試験（生成器を使う end-to-end）は依存する SHA を固定して行う。意味論、一般補題、文書上の probe は #160 のマージ前でも進めてよい。マージ操作はユーザーが行う。
- 現状の記録: この枝の plain `#ved_u1` は `Signal.loop` 形の register 子を `[proof]` で拒否する（§6 probe1）。`Tools/VedU1Deep.lean` は base にもあるが、#160 の multi-register/Bool 拡張は未統合。

## 6. 代表と最初の阻害（設計 probe。測定ではない）

### 6.1 inventory との関係
固定 327 行の一覧（results.tsv）はこの worktree の外にあり、読まなかった。したがって inventory の行番号と宣言との照合は、この単位では行っていない。次の単位で、coder が一覧と宣言を照合し、最初の阻害を記録する（Q9）。現時点の記録:
- reviewer 提出時の補足にある baseline の u1_deep prep_error 'single-module' 36 行（R9 R10 R65 mesh2x2 R67 R68 R92 R94 R126 R127 R162–R164 R184–R188 R192–R195 R210 R211 R220 R223 R224 R227 R228 R230–R232 R235 R236 R246–R248）が候補集合だが、各行の宣言との照合は未了。
- 木にある宣言から形を判断した限り、H2 単独（単一出力、register 子、深さ 1）の行は見つかっていない。照合の結果、H2 単独の行が無ければ「無い」と報告する。小例は 327 に加算しない。
- `Tests/Compiler/MultiInstanceTest.lean` の `mesh2x2`: 親は組合せ、`pe` は register 2 個で構造体出力（aOut/pOut）、4 instance。H2＋H3（複数出力）。H2 単独の代表にはならない。
- `synth_keccakRc`（`keccakRcHW`）、`synth_sha256KMux`（`kMux`）、`synth_aesRcon`（`rconHW`）: 木にある宣言を読む限り、どれも `@[hardware_module]` の組合せ関数（`kLut!`）を `#synthesizeVerilog` するだけで、register を持つ子はない。この種の行は H2 の候補ではない。これらが [order] で拒否される原因は調べていない（H2 の範囲外）。
- `synth_spongeD0`: 親 `keccak256SpongeHW` は register を多数持ち、子 `wKeccakF` は複数出力（`KeccakFOut`）で内部に register を持つ。H2＋H3、規模が大きい。
- 単一出力で register を持つ子を持つ宣言は既存テストにある: `Tests/Compiler/Issue107LetBoundInstanceDup.lean` の `oneInstance`/`threeInstances`（子 `toggle` は Bool、register 1 個、親は register を持つ。`threeInstances` は同一子 3 instance）、`Tests/Ved/NestedCacheCheck.lean` の `parentMix`（子 `accMod`: 8bit register 1 個、親は register 1 個）。これらは小例で、327 には加算しない。

### 6.2 probe（scratch は /build 配下、複製を $KJOB_REPORT_PATH の隣に置いた）
- 手順: `kjob lake build Tools.VedU1HierEntry` の後、`kjob lake env lean <file>` のみ。注: manager PR #80 は未配備で、lake env が他の job の olean を見ている可能性がある。この結果は設計判断のための probe であり、測定ではない。
- 宣言: 子 `accMod x := Signal.loop fun s => Signal.register 0#8 (s + x)`（register 1 個、8bit）。
- probe1（/build/h2probe/Probe.lean、複製 `<report dir>/probe/Probe.lean`）:
  - `#ved_u1_hier H2Probe.parTwo`（親は組合せ、`accMod` を 2 instance）: `VED U1 REFUSED H2Probe.parTwo [hier-shape]: instance _tmp_inst_H2Probe.accMod_0: child H2Probe.accMod is not a combinational leaf (register, memory or instance in its body: H2)`。最初の阻害は H1 の shape 検査（意図どおり）。
  - `#ved_u1_hier H2Probe.parReg`（親が register を持ち子も register）: `[hier-shape]: top statement reg _tmp_loop_body_4 … is not an assignment or an instance (registers or memories at the top are not in H1)`。
  - `#ved_u1 H2Probe.accMod`（子単体、この枝の plain `#ved_u1`）: `[proof]: errors were logged while elaborating the proof; first: unsolved goals … Signal.loop`。この枝の plain `#ved_u1` の生成器は register を持つ `Signal.loop` 形の単独証明に届かない。`Tools/VedU1Deep.lean`（`#ved_u1_deep`）は base にも存在するが、#160 の multi-register/Bool 拡張は未統合（この probe は #160 の生成器では測っていない）。
- probe2（/build/h2probe/Probe2.lean、複製 `<report dir>/probe/Probe2.lean`）: `synthesizeCombinational` が返す `(m, d)` を表示。
  - 親 `parTwo` の body: `inst accMod _tmp_inst_H2Probe.accMod_0 [clk↦ref clk, rst↦ref rst, _gen_x↦ref _gen_a, out↦ref _gen_p]` と `…_1`、`assign _gen_out (sub _gen_p _gen_q)`、`assign out`。親の inputs は `[_gen_a, _gen_b, clk, rst]`（親は register なしでも clk/rst を持つ）。
  - 子 `accMod` の body: `assign _tmp_reg_input_1 = _tmp_loop_0 + _gen_x`、`register _tmp_loop_body_2 clk (rst, sync) ← _tmp_reg_input_1 (init 0)`、`assign _tmp_loop_0 = _tmp_loop_body_2`、`assign out = _tmp_loop_0`。2 instance とも register 名は `_tmp_loop_body_2`（鍵が path を含む必要の実例）。
  - instance 名は `_tmp_inst_H2Probe.accMod_0` のようにドットを含む文字列。path の鍵としては単なる文字列。生成する証明テキストでの綴りは H1 の private 名の扱いと同様に注意が要る。
- 計測値（heartbeat、時間、メモリ）は取っていない（設計 probe）。
- 未確認（実装前に確認する事項）: DeepElab（`#verify_elab_deep`）が `@[hardware_module]` の呼び出しを含む親宣言に対して定数を生成できるか。親全体を DeepElab に渡すと single-module 拒否になる可能性がある。その場合の経路は §2.2 の 1 と §12 の単位 1（子呼び出しを自由 signal にした open 親を reify し、元の親との等式をカーネルで検査する）。

## 7. 実装時の対照
H1 の対照（`Tests/Ved/U1HierCheck.lean`）と同じ方式（`checkU1H` を 1 箇所だけ変えた `(m, d)` に走らせ、名前の付いた段で拒否、base の定数が残らないこと）。型レベルの対照は `elabTermEnsuringType` の拒否として書く。

「すべて拒否」ではない。instance 名の一貫した改名や、対称な子の入れ替えは意味を保存することがある。拒否するのは意味が変わる変更と、結びつきの無い証明だけで、意味を保存する変更は肯定対照にする（P2-2）。

拒否の対照（非対称な例で意味が変わることを示す。2 instance に異なる入力を与え、出力を非対称にする）:
1. 子の register init を変える（`regsOf` の init）: 子の `OutputsStmt` が成立しない／`st0H` が宣言とずれる。
2. 子の next 値（register 入力式）を変える: 子の定理との不一致。
3. 誤配線: 2 instance の出力接続（`p`/`q`）または入力 conns を取り違える。`out = p - q` のような非対称な関数では出力が変わり、宣言と食い違う。
4. 親の register が間違った instance を読む（`ref` の取り違え）: 出力が変わる。
5. 共有状態: 鍵を (path, 名前) ではなく名前だけにした変異版 `stepHS`（「module ごとに 1 状態」の実装誤り）で、2 instance の出力が食い違うことを concrete 値で確認し、その変異版では文が成立しない。
6. 1 cycle のずれ: 子の出力を 1 cycle 遅らせて（register 段を 1 つ足す、または seed の時間添字をずらす）観測する。入力が変化する stream で、出力が宣言と食い違う。
7. 子の定理が結ばれていない・別値: 同名の module だが値（body、init）が違う定義の証明、`d` から解決した module に束縛されない（`decide` が通らない）証明、未接続の証明。値が同じで定理が正しい別 run 由来の証明は、拒否ではなく使用可（肯定側）。
8. 追加: 子の clk を親の clk 以外に接続、子の rst を定数に接続、子の register 重複名、register 出力への assign（多重 driver）、instance を通る組合せ循環。

肯定の対照:
- `stepHS` を concrete 値で評価し、宣言の値と比較する。2 instance に異なる入力を与え、状態を 2 cycle 以上進める。
- instance 名の一貫した改名（全 `inst` の名前と `wrsH`/conns の参照を同時に改名、`st0H` の path も追随）: 受理され、出力 stream が改名前と同じ。
- 対称な 2 instance の入れ替え（同じ子、conns と instance 名を一貫して入れ替え、親の式も追随）: 意味が保存される場合は受理を確認する。入れ替えで意味が変わる場合（非対称な親の式）は拒否の対照 3 に属する。
- 別 run 由来で値の同じ子定理の使用（上の 7）。
- 小例は 327 に加算しない。

## 8. 費用とリスク
- 証明の大きさ（未測定の見込み）: 親の open step 補題は親 register 数に比例する、と期待している（Deep の slot ごとの `simp`）。子ごとの `OutputsStmt` は子の register 数に比例し、instance 数 × 子の register 数では増えない、と期待している（同じ子の定理を `d` から解決して再利用する）。いずれも未測定であり、実測は次の単位以降で行う。射影補題と L2/L3 の適用は instance ごとに 1 回、と見込んでいる。
- heartbeat: #160 の記録のとおり、複数 register＋複数入力で既定の heartbeat を超える例がある（`[checker]` で拒否、受理はしない）。大域上限は上げない。H2 でこれが親・子それぞれの証明に加算される。
- 分割する補題（slot ごと・instance ごと）:
  - 一般補題（module に依存しない、1 回だけ証明）: L1〜L6、`childNext_agree`、`runHS_proj`、`runHS_stateless`、`st0H_own`、`st0H_slice`、`seed_regs_only`、`runModule_prefix`。
  - slot ごと: 親の register の不変条件（Deep の生成）。
  - instance ごと: 子の定理の束縛（`decide`）と `ChildRel_i`、(F2) の適用（生成テキスト）。
- 主なリスク:
  1. 親の抽象化 `f = F (g x_1) … (g x_n)` の生成（let 束縛の部分 signal の特定）と、元の親との等式の kernel 検査。`kabstract` の成功だけでは足りない（§12 単位 1）。
  2. DeepElab が hardware_module 呼び出しを含む親を扱えるか（未確認、§6）。
  3. 値の範囲の不変条件（L6）の追加。
  4. instance 名のドットや private 名の、生成する証明テキストでの綴り（H1 で private 親が 1 件出ている）。
  5. 子の組合せ経路の保守的な扱い（§4）による偽の拒否（順序回路として合法でも拒否しうる）。
  6. 子の run の存在・射影の証明順（§2.5）が、実際の `evalAssignsI` の fold 順と噛み合うか。
- 補題の本数や規模は見積りで、「1 本で済む」とは言わない。

## 9. reviewer への質問（裁定済み）
Q1〜Q9 は reviewer の裁定を得た。各裁定と本文への反映は §11。質問の原文は次の要約のとおり。
1. 状態の表現。2. 子の next 値の求め方。3. 文の形（置換か別定義か）。4. 初回スライス（H2a か H2b か）。5. instance を通る組合せ循環の扱い。6. 子 clock/reset の検査位置。7. #160 への依存。8. 親の抽象化の probe の単位。9. 代表の指定。

## 10. 根拠
- 設計: docs/VED-HIER-DESIGN-v1.md §7、§8。
- コード（ved/hier-h1 2a8ff165）: Tools/VedU1HierSem.lean（`stepH`、`runH`、`WOH`、`evalAssignsI_perm`、`IELaws`）、Tools/VedU1HierComp.lean、Tools/VedU1Hier.lean（`HierShape`、`OrderOkH`、`AdmArr`、`OutputsOnH`、`U1HStmt`）、Tools/VedU1Contract.lean（`regsOf`、`st0`、`OrderOk`、`OutputsStmt`、`U1Stmt`）、Sparkle/IR/Semantics.lean（`regNexts`、`applyNexts`、`stepModule`、`runModule`）。
- 別枝: `git show ved/multireg:Tools/VedU1Deep.lean`（PR #160、multi-register/Bool U1、slot 不変条件）。`Tools/VedU1Deep.lean` は base にも存在する。
- probe: /build/h2probe/Probe.lean、/build/h2probe/Probe2.lean（複製: `$KJOB_REPORT_PATH` と同じディレクトリの `probe/`）。ログ・測定値はこの木に置かない。

## 11. reviewer 裁定（2026-11-11、対象 12135944）と反映
方向の許可であり、H2 の実装、文の凍結、strict 件数、Issue の完了、release の承認ではない。

### 裁定
1. **Q1 → (a)** `Path → String → Nat`。path は instance 名のリスト、root = `[]`。同じ module の複数 instance を区別し、解決済みの実 register だけを読み書きする。→ §0、§1.1。
2. **Q2 → (a)** 最終 env からの再評価で開始。ただし `childNext_agree` を状態固定の `IELaws`/`Good` から証明し、子の入力・出力・次状態の一致を分ける。全 next を更新前状態から作り、最後に同時更新する。→ §1.2、§2.4 L3。
3. **Q3 → (b)** 最初は別定義 `U2HStmt` / `runHS`。既存の `U1HStmt` / `runH` は置換せず、H1 の保証・CI・測定は固定。H1 の条件下で `runHS_stateless` と葉の `runModule` との対応を証明してから統一を検討する。→ §0、§1.6、§3。
4. **Q4 → (a)** H2a（register なしの親、同じ register 子の 2 instance）→ H2b。最初の例は異なる入力と非対称な出力で、共有状態を観測可能にする。→ §5、§7。
5. **Q5 → (a)** 子の各出力が全入力に依存するとみなす保守的 `WOH`。順序回路として合法な回路を拒否しうることを明記する。精密な循環解析は後続。→ §4、§8 リスク 5。
6. **Q6 → (a)** shape と意味論の両方で検査する。意味論の clock/reset 判定は module と接続から定義し、契約を参照しない。→ §1.3、§1.5、§4。
7. **Q7** #160 の生成器（`#ved_u1_deep` の multi-register/Bool）を再利用し、plain U1 の別拡張はしない。統合試験は依存 SHA を固定する。意味論・一般補題・文書 probe はマージ前に進めてよい（マージはユーザー）。→ §0、§5。
8. **Q8** 親の抽象化と型を確認する小さな別単位を先に切る。親全体を DeepElab に渡すと single-module 拒否があり得るので、子呼び出しを自由 signal にした open な親を reify し、元の親との等式をカーネルで検査する経路を試す。`kabstract` の成功だけは等式の証拠にならない。→ §2.2、§6.2、§12 単位 1。
9. **Q9** H2a の `parTwo` 相当 → H2b の `parentMix`。`threeInstances` は次の回帰。固定 327 は coder が一覧と宣言を照合して最初の阻害を記録する。H2 単独の行が無ければ無いと報告し、小例は件数に足さない。→ §5、§6.1（照合は未了、次の単位）。

### 指摘と反映
- **P1-1（§2.4）** 旧 `runHS_proj` の右辺 `envs.map (childEnvOf i cs)` は、親の Env だけから子の全内部 Env を再構成する形で、出力に届かない子の register の状態が親 trace から分からないため一般には不足する。→ §2.4 を書き直した。存在量化した子 trace `cenvs` と、入力 port・出力 port・register 状態の対応（補助の子状態履歴 `runModuleTrace`）で述べる。conns から子の全 Env の等式を主張しない。初期値の一致は `st0H` のスライスの補題 `st0H_slice` で別に供給する（§1.3）。
- **P1-2（§2.2–2.5）** 射影が成功した hier run を前提とし、§2.5 が子の `OutputsStmt` から run の存在を得る循環。→ §2.5 を cycle 帰納（不変条件 I1〜I3）と `WOH` の fold 順で子の入力履歴を延長する証明順に書き直した。`OutputsStmt` は初期状態からの run の性質で、任意状態の 1 step の成功は子の shape（`OrderOk`/`AdmArr`）から得る。有限 prefix と stream の扱い（`runModule_prefix`、`srcOf` の因果性を使う経路は採らない）を明記した。親の宣言が期待する入力 signal と実 conns stream の一致 (F2) を子定理とは別に供給する（§2.1）。
- **P2-1（§1.3/§1.5）** 「clock の値は意味論に現れない」を、register 更新が clock edge を検査しないことと、`Expr.ref` が clock 入力を読み得ることに分けて限定した。`InputsOk` の clock 全称・reset = 0 は維持（`clock = 0` 固定や幅条件の追加をしない）。§1.3 の子契約から clock 名を読む記述を、module と conns だけの判定 `clkRstOk` に改め、§1.5 と整合させた。親子の局所名の違いと別 clock への接続を区別し、「同名のみ」を選ぶ場合はそれが被覆の制限であると明記した。
- **P2-2（§7）** 「すべて拒否」を撤回。一貫した改名・対称な入れ替えは肯定対照にした。誤配線・共有状態・1 cycle のずれは非対称な例で反駁する。値が同じで定理が正しい別 run 由来の証明は使用可で、拒否するのは同名で値が違うものと、`d` に結ばれていない証明（§2.2、§7）。

### 記録の訂正
- 「この枝には `#ved_u1_deep` がない」を、「`Tools/VedU1Deep.lean` は base にも存在する。#160 の multi-register/Bool 拡張が未統合」に直した（§0、§5、§6.2）。
- 費用の「register 数に比例」は未測定の見込みと明記した（§8）。

## 12. 次の単位と、未決定の事項

### 次の単位（順序）
1. **Q8 open 親の抽象化 probe（型付き、小さい）**: 子呼び出しを自由 signal にした open 親を reify し、元の親宣言との等式をカーネルで検査する。`kabstract` の成功だけを根拠にしない。親全体を DeepElab に渡した場合の single-module 拒否の有無も記録する。
2. **型付き `runHS` / `runHS_proj`（存在量化した子 trace）/ 存在証明の構成と `runHS_stateless`**: §1〜§3 の定義、§2.4 の射影、§2.5 の証明順に従う。H1 の条件下で `runHS_stateless` と葉の `runModule` との対応を先に証明する。
3. **H2a の最小 end-to-end probe（`parTwo` 相当）**: register なしの親、同じ register 子の 2 instance、異なる入力・非対称の出力。#160 の生成器を使う統合は依存 SHA を固定する。
- 並行して、固定 327 の一覧と宣言の照合（最初の阻害の記録、H2 単独の行が無ければその報告）を coder が行う（§6.1）。

### 未決定
- H2 の実装は承認されていない。
- `U2HStmt` / 射影補題などの文（statement）は凍結されていない。
- strict 件数（327 への加算）は承認されていない。小例は件数に足さない。
