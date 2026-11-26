# VED 階層 H2 単位3: H2a end-to-end（register なし親・register 子の複数 instance）

基準: int/h2a（H2 単位2 `ved/hier2-sem` + 単位1 `ved/hier2-open` + PR #160 `ved/multireg` のローカル統合）。
設計: docs/VED-HIER-H2-DESIGN.md。本文書は実装記録であり、文の凍結、327 行への加算、hierarchical strict
の inventory 主張、release を主張しない。小例（`parTwo` 等）は 327 に加算しない。

## 1. 範囲（H2a）

- 深さ 1、register を持たない親、葉の子（assign と register のみ、出力 1 個）。
- instance の入力 port の接続は、すべて親の **入力** への `ref`（データ port は親のデータ入力、子の
  clock / reset port は親の clock / reset 入力）。内部 wire や導出式・別 instance の出力を instance の入力に
  する形は `[conns]` で拒否する（F2 を内部 wire に広げるのは次の単位）。
- 親が register を持つ形（H2b, `parentMix`）は `[scope]` で拒否する。instance を 1 つも持たない親は `#ved_u1`。
- 子の定理は #160 の生成器（`#ved_u1_deep`: multi-register / Bool）。register を持つ子は事前に
  `#verify_elab_deep <child>` が要る（`#ved_u1_deep` と同じ前提）。register なしの子は plain 生成器。

## 2. ファイル

| ファイル | 内容 |
|---|---|
| `Tools/VedU2HierOrder.lean` | `OrderOkHS`、`OrderHS`、`orderOkHS_sound`、`orderOkHS_hwr`（`hwr` を導出） |
| `Tools/VedU2HierStmt.lean` | `OutputsOnHS` / `OutputsStmtHS` / `U2HStmt`、`exists_arrHS`、`oracleIE`、`fold_oracle`、`open_eq_evalAssigns`、`closed_fold_is_open`、`runHSTrace_cycle` / `runHSTrace_open`、`outputsOnHS_of_oracle` |
| `Tools/VedU2HierKid.lean` | `kid_inst`（instance の出力を子の実定理から）、`insCIn`、`connsIn` / `dataIn` と soundness、`runModule_congr_seed` |
| `Tools/VedU2HierEntry.lean` | `#ved_u2_hier`、`checkU2H`、`genOpen`（open 親の生成）、証明スクリプトの生成、診断 |
| `Tests/Ved/U2HierCheck.lean` | 入口の実行、正確な型、std3 機械判定、具体的な閉じた run、clock/reset、37 本の拒否対照、肯定対照 |
| `Tests/Ved/U2HierPin.lean` | `runHS_proj` / `ProjAt` / `U2HStmt` / 意味論定義の型の独立な再記述と固定、実 design 上の意味対照 |

## 3. 文の型

```
def U2HStmt (c : Contract) (m : Module) (d : Design) (f : c.table.Ty) : Prop :=
  CorrStmt c ∧ ShapeCore c m ∧ c.clkRst = designClkRst d m ∧ HierShapeS d m = true ∧
  regsOf m.body = [] ∧ WidthStmt c m ∧ OrderHS d m ∧ (∀ x ∈ d.modules, OrderStmt x) ∧
  (∃ arr, AdmArr d m arr) ∧ OutputsStmtHS c m d f

def OutputsStmtHS c m d f := ∀ arr, AdmArr d m arr → OutputsOnHS c m d arr f
def OutputsOnHS c m d arr f := ∀ ins, InputsOk c m ins → ∀ K, ∃ envs,
  runHS d arr m (seedFwd m K ins) K (st0H d m) = some envs ∧
  ∀ t, t < K → ∀ o ∈ c.outputs, ∃ env, envs[t]? = some env ∧ env o.name = srcOf c f ins o.name t
```

最終定理は `decl.ved_u1 : U2HStmt decl.ved_contract decl.ved_mod decl.ved_design decl`（`decl` は元の宣言の定数）。
型に `ExprsSupp` / `ChildSucc` / `htie` / `hwr` / `InputsOk` などの未供給 binder は無い。`htie` は文の連言肢
（`c.clkRst = designClkRst d m`、decided）、`hwr` は `OrderOkHS` から導出、`ExprsSupp` は decided、`ChildSucc` は
子の実定理から `childSucc_of_outputsOn`、`InputsOk` は文の量化の内側。

## 4. 入口の段階（`vedU2HierEntry`）

1. `table` / `multi-output`（synthesis より前）。
2. `synthesis`: `synthesizeCombinational` を 1 回。返却 `(m, d)` を保持。
3. `artifact`: `ved_mod := toExpr m`、`ved_design := toExpr d`（評価し戻して比較）。
4. `hier-shape`: `HierShapeS d m`（診断付き）。**`HierShapeS` 単独は soundness 検査ではない。**
5. 契約: 宣言の型の table + 親の後ろ 2 入力を clock/reset とする。`CorrStmt`、`c.clkRst = designClkRst d m`
   （`[clkrst]`）、`ShapeCore`、`WidthStmt`。名前は実名で比べる。
6. `order`: `OrderOkHS d m b0`（重複 register 出力、register と assign / instance 出力の衝突、入力への書込み、
   register 入力を含む undriven read、instance を通る組合せ循環（保守的: 子の各出力は全入力に依存）、
   出力の driver 欠落）。
7. `scope`（register あり親、instance なし）と `conns`（instance 入力が親入力でない）。
8. `child`: `d.modules` の各 module を `d` から取り、`decl.ved_child.<module>` に子の U1 定理（register ありは
   `buildDeepWith`、なしは `.generated`）。
9. `open`: 宣言の本体から子呼び出しを抽象して `decl.ved_open` を生成（`kabstract` は構成の道具）、等式
   `decl a b = decl.ved_open a b (g a) (g b)` を **kernel に** `decl.ved_open_eq`（証明は `rfl`）として追加。
10. `type` / `proof` / `kernel` / `audit`: 完全な期待型に対し生成した証明を elaborate、同期的に `addDecl`、格納型を
    再構成した期待型と比較、`strictAudit`（std3）。失敗は `saveState` の restore（定数・メッセージが戻る）。

## 5. 証明の構成

- `kid_inst`: 閉じた run の各 cycle で、instance の出力 wire は子の `OutputsStmt` を総ての stream
  `insCIn cs ins`（子の各入力 port を、接続された親入力の stream から読む）に適用した値。子の run は
  `runHS_proj` の `runModule`（`insCOf`、有限）。seed が実行 cycle で一致するので `runModule_congr_seed` で
  結ぶ（因果性の補題は使わない）。範囲: データ port は親のデータ入力（親の `InputsOk`）、子の reset port は
  契約の reset（`instPair_tie` と `htie` で 0）、clock port は親の clock 入力（範囲仮定なし）。これが F2。
- `fold_oracle`（L2）: 閉じた fold（`instEvalS`）が `E` なら、instance 出力を oracle（=`E` の値）にした open fold
  も `E`。`open_eq_evalAssigns`: その open fold は IR 自身の open 意味論 `Sparkle.IR.Semantics.evalAssigns`
  （instance は no-op、出力は自由入力）と一致。`runHSTrace_open`: 成功 run の各 cycle の env はその open 評価。
- `outputsOnHS_of_oracle`: run の存在（`runHS_exists`）、各 cycle の env は open fold の `E`（一意性）、
  `hopen`（open 親の meaning、生成した `decl.ved_open` について同じ `(m, d)` 上で simp）と `hkid`（`kid_inst`）から
  出力 = 宣言の値。

## 6. reviewer 条件

1. 受理用 shape/order: `OrderOkHS` と子の `OrderStmt`、`hwr` 導出。制御は §7 の 1–9、`HierShapeS` 単独を
   soundness と呼ばない（`Tools/VedU2HierOrder.lean` 冒頭、`Tools/VedU2HierStmt.lean` 冒頭）。
2. clock/reset: 実 Contract との tie（連言肢 `htie`、`CorrStmt` の実名の単射性、`ShapeCore`）。拒否対照（親の正しい
   table 固定）: データ入力を reset に、定数 reset、データ入力を clock に、clock と reset の入れ替え、契約を design の
   対に強制すると実名が重なり `CorrStmt` が拒否。肯定対照: 変化する clock と reset 0（最終定理の具体的な適用
   `parTwo_changing_clock`）、全称 clock（`parTwo_any_clock`）。reset ≠ 0 は文の範囲外（`insRst_not_ok`）で、実際に
   run が宣言と違う。"_gen_a and a overlap" の記述は撤回し、実名で書き直した（`U2HierSemCheck`）。
3. 文の固定: `Tests/Ved/U2HierPin.lean`。`runHS_proj` / `ProjAt` / `insCOf` / `U2HStmt` / `applyH` / `stepHS` /
   `st0H` を primitive な項で独立に再記述し、それぞれ補題・`Iff.rfl` / `rfl` で証明。型を `#guard_msgs`
   （完全修飾名）で固定。対照: 別 path、別の子、誤った初期状態、1 cycle のずれ、port 対応の欠落、共有状態、肯定対照:
   instance 名の一貫した改名。std3 の機械判定: `std3Only`。

## 7. 対照（`Tests/Ved/U2HierCheck.lean`、各拒否は段階と原因の語を検査し、定数が残らないことも検査）

親の netlist: 重複 register 出力、register 対 assign、register 対 instance 出力、入力への書込み（assign、
instance 出力）、undriven register 入力、instance の自己ループ・相互ループ、undriven 入力 wire、出力 driver 欠落。
子の netlist: 重複 register 出力、register 対 assign、undriven register 入力、入力への書込み（`not sane`）。
clock/reset: 上記。配線: 入力 conn の取違え、出力 wire の入替え、conn の欠落・余剰・重複、幅違い、非 wire。
子: 本体改変、init 改変、別 run の同名 module。design: 別 design、未使用の余剰 module、重複名、top 不一致、module 欠落。
scope: register あり親、導出 wire の instance 入力、instance なし、多出力。型レベル: 別宣言の証明、別 design、別の子の証明。
肯定: instance 名の一貫した改名、instance の入替え、3 instance、同じ入力の 2 instance、組合せの子との混在、
2 register + Bool の子。

## 8. 実測で見つかったこと

- **単位2 の `connsOkS` は実 synthesizer の親を拒否していた**: 親は clk/rst の wire を宣言しないので、子の
  clk/rst port への接続の幅検査（`declWidth m x == p.ty.bitWidth`）が必ず偽になり、register を持つ instance を
  持つ親はすべて `HierShapeS` で拒否された（単位2 の手書き design は clk/rst wire を持っていた）。本単位で、
  子の clock / reset port（`isClkRstPort`）だけ幅検査から除いた（`Tools/VedU2HierProj.lean`、他の条項は同じ）。
- 子の register の init を両 instance で同じだけ変えても `p - q` では打ち消され観測できない。init の対照は
  非対称（片方の instance だけ）にした（`U2HierPin`）。
- 出力 port の接続を欠いた instance は、意味論自体は未駆動 wire を seed 値のまま走る（`some`）。拒否するのは
  shape 検査（`HierShapeS`）であり、入力 port の接続欠落は意味論でも `none`。
- `Module` の `==`（`deriving BEq`）は kernel で簡約できない。kernel で評価する対照は module 名の `==` を使う。

## 9. 未了

- H2b（register を持つ親）、instance の入力が内部 wire・導出式・別 instance の出力である形（F2 の一般化）、
  多出力の子（H3）、深さ 2 以上。
- 子の `#verify_elab_deep` を入口が自動で走らせることはしない（前提として要求し、無ければ `[child]` で拒否）。
- 固定 327 の一覧と宣言の照合（H2 単独の行の有無）は本単位では行っていない。
