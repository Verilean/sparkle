# G0 + G1 + W1 の結果と W1 の確認 (a)〜(e)

Issue `sparkle-gd-g01w1`（agent gd01）。型は `scripts/gen5/GDCOVER01_FREEZE.md`（ea7d4866）のとおりで、elaborate で型の意味は変わらなかった（namespace の置き場所だけ: G0 は `Tools.ShippingGen5Acc`、G1/W1 は `Tools.ShippingGen5GDCover1`）。台帳: FG 102 / T1 54（今回 FG -0 +0 / T1 -0 +0）。**C.CV-5 は条件付き・未計上のまま**（下の表で (c)(e) が未解決）。

## 実装した範囲

| 段 | 名前 | 結果 |
|---|---|---|
| G0 | `genDataC`, `genDataC_isSome_iff`, `reachCover_iff_sdw` | Pod の target build で通った（標準 axiom のみ） |
| G0 | `peel_of_machineShape` | **`unfold machineShape?` で通った**（SURVEY §7 の「unfold で通るか未確認」は、通る、で確定。`symbolicMode || !parameters.isEmpty` の `if` は `rfl` で `false` に落ちる。止まる点なし）。結論は `E = .defnInfo d` を含む形（ロードマップの `E.value` の略記を具体化） |
| G1 | `StateSideWitness`, `stateSide_of_production` | 通った。`hbr` は C.CV-4 の今の文（Cover5.lean:97 と同じ）。`st` を保つ |
| W1 | `shapeAgree_witness`（`dataOfAt` 版）, `shapeAgree_witness_from`（`dataOfFrom` で `tin` / `fl` 任意） | 通った。`ShapeAgree d st` の `st` は G1 の witness と同一 |

Check: `Tests/Gen5/GDCover01Check.lean`（G0 と G1/W1 を 1 ファイルにまとめた。freeze の「2 ファイル」から変更、意味の変更なし）。TYPE 8（Pi 2 + 定理 6）/ BODY 2 / MUTANT 17（単独 15 + 複合 2、**signature / defeq での棄却であって意味的反例ではない**）/ AXIOMS 8 件すべて標準 3 つ / CLOSURE 8537 constants（禁止定数なし、未知定数 0、supplier 6 個が root と別に到達）、walker 制御（負 4・正）と unknown 制御（負 3・正 1）。
defeq のみで受理された箇所（構文一致ではない）: `reachCover_iff_sdw` の binder `hloc`、`stateSide_of_production` / `shapeAgree_witness(_from)` の binder `hbr`（Check の `Cv4` 定義 vs inline）と結論（`StateSideWitness` の展開）、`genDataC` の body の結論。sorry の警告 3 件は walker の負例（意図的）。

## W1 の確認 (a)〜(e)

読んだもの: C.CV-5 / C.DO-3 の行の原文（`scripts/gen2/premise_ledger/C_M5dg.md` @par/fg-ledger-sync の §8 CV-5、§5 DO-3）、Cover5.lean（base）の `shapeAgree_of_sides` / `shapeAgree_of_fuel_run` / `shapeAgree_of_production` の binder、DG_DATAOF_FREEZE §10、`Tools/ShippingGen5DataOfDims.lean`。

| # | 確認 | 結果 | 根拠・条件 |
|---|---|---|---|
| (a) | C.CV-5 の行と Cover5 の binder が同じ束縛・同じ domain か | **一致**（`d` / `sp` / `hsp hss hls hn` と `hs` の 4 連言）。ただし W1 には行に無い binder `lvl`（`dataOfAt lvl` の引数）と `hd` が付く | 行の原文: `hsp : d.shape = sp`, `hss : d.ss.length = sp.layout.slots.length`, `hls : d.ls.length = sp.layout.lets`, `hn : sp.insts.length ≤ d.nIn`, `hs`（4 連言）。W1 の `ShapeAgree d st` はこの 5 つを `shapeAgree_of_sides` で束ねた結論と同じ（`st` は G1 の witness の `st`）。行の「`s = sp` は未供給（消費側の仮定）」は、W1 が `h : machineShape? … = some sp` と `hd : dataOfAt lvl E senv sp = some d` を**同じ `sp`** で取ることで型の上では閉じる |
| (b) | d の量化 | **食い違い**: 行の `d` は消費側の自由な `d`（仮説 `hsp…` を取る形）で、W1 は `dataOfAt lvl E senv sp = some d` を満たす `d` に限る | W1 の出力が行を置き換えるのは、消費側の `d` が `hd : dataOfAt lvl E senv d.shape = some d` を満たすときだけ（`GenData.hdata` は `dataOf E senv d.shape = some d` なので、`dataOf := dataOfAt lvl` のときは満たす）。`dataOf` を何にするかは (c) |
| (c) | carrier（`dataOfAt` / `dataOfAtP`） | **未確定（食い違い扱い）**: 消費側の `dataOf` が `dataOfAt lvl` に固定されているかは、この調査では見つからなかった（C 分類: 閉包が未固定） | `shapeAgree_witness_from` は `tin` / `fl` について一般なので、`dataOfAtP` を採る場合も同じ証明で通る見込みだが、`dataOfAtP` は未定義（D3 は未判断）。この単位は carrier を選んでいない |
| (d) | g5do-r6 の dims が base に入っていて build できるか | **一致**: `Tools/ShippingGen5DataOfDims.lean` は base f18eb040 にあり、lakefile に `lean_lib` があり、この Pod の target build（`Tools.ShippingGen5GDCover1` 経由、734 jobs）で通った | DataOfDims 自身の clean issue-linked build は未実施（ファイル header は "agent build のみ、clean build は coder"）。coder が clean build を実行する |
| (e) | C.DO-3 との重複 | **食い違い（原文が一致しない）**: 台帳 §8.1 は「C.CV-5 と C.DO-3（row 6b）」と書くが、C.DO-3 の原文は "row **6a**, C-CMP, C-QWIT, S-OK, S-COV-FLOAT, `dataOf at exprSize`"（名前のみ）で 6b を含まない | row 6a（state 側）は W1 では G1 の `StateSideWitness` が与える（C.CV-4 を仮定）。DO-3 の 6a と CV-5 の `hs` が同じ義務かはこの調査では判定していない。どちらも減算に数えない |

**まとめ**: (a)(d) は一致、(b) は条件付き、(c)(e) は未確定・食い違い。よって **C.CV-5 は「条件付き・未計上」のまま**。台帳差分は 0/0。(c) には D3（carrier の意味の変更）、(e) には台帳の記述の修正が要る可能性があり、どちらも reviewer 側の判断が要る（この単位では選んでいない）。

## 残り

- clean build は coder（`Tools.ShippingGen5GDCover0`, `Tools.ShippingGen5GDCover1`, `Tests.Gen5.GDCover01Check`、`Tools.ShippingGen5DataOfDims`）。
- 次の段: G2（条件 2 の binders 長）は G0 / G1 を使う。W3 は先に Bool let / 冪等の確認。
