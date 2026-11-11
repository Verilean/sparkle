# VED 階層 H2c: 子の data 入力が親の net（親 data 入力だけから計算される wire）のとき

基準: ved/hier2-h2b a8f3b7d2（H2b）。設計: docs/VED-HIER-H2-DESIGN.md（§2.1 の F2、§11、§12）、docs/VED-HIER-H2B.md。
本文書は実装記録であり、文の凍結、327 行への加算、hierarchical strict の inventory 主張、release を主張しない。小例は 327 に加算しない。

## 0. 結論

- **文 `U2HRStmt` / `U2HStmt` は変更していない**（`Tools/VedU2HierReg.lean`、`Tools/VedU2HierStmt.lean` は H2b と差分 0。型は `Tests/Ved/U2HierWireCheck.lean` で入口の期待項と比較し、`example` で書き下している）。binder は増えていない。
- 一般化できたのは「子の data port が、親の data 入力だけから（assign の連鎖で）計算される net を読む」場合まで。`#ved_u2_hier` はこれを strict（標準 3 axioms）で受理する。
- **固定 14 行は 1 行も strict にならない。理由は 2 つ、独立**:
  1. 14 行すべてで子 instance の入力は **親の register 出力**（または register を含む式、別 instance の出力）。register は `Signal.loop` の中にあり、宣言の呼出し引数がループに束縛されるため、親入力の閉項として書けない（§3）。これは H2c の範囲外で、`[conns]` に分類して拒否する。
  2. 7 つの子の葉（httpGetByte、httpRespByte、arpPacketByte、icmpHeaderByte、ipv4HeaderChecksumSig、respByteMux、SHA512HW.kMux）は、**どれも単体の `#ved_u1` が strict でない**（§4）。1 が解けても 14 行は通らない。

## 1. 変更

| ファイル | 内容 |
|---|---|
| `Tools/VedU2HierNet.lean`（新） | `kid_inst_net`（`kid_inst` の一般化: 子の data port は全域の流れ `F` を読み、clock/reset は親入力のまま）、`closed_run_asg` / `closed_run_asgOf`（閉じた run の各 cycle で、検査済み arrangement の全 assign が成り立つ: `Good` から）、`netIn`、`connsNet(_sound)`、`asgOf`、`sig_of_obs_bv/bit` |
| `Tools/VedU2HierEntry.lean` | `CallInfo.derived/argDefs`、`InstInfo.derived/chain`（既定値付き）、`genOpen` に `allowDerived`（既定 false: H2a は変わらない） |
| `Tools/VedU2HierRegEntry.lean` | 親 register ありの入口だけ: conns 検査を `connDiagNet`（clock/reset は親入力、data port は親 data 入力か純 net、理由の分類）に拡張、導出呼出しの対応付け（検査済み arrangement の順、同じ inlined net は同じ呼出し）、`kid_inst_net` を使う生成証明（`hrange` / `hrunF`） |
| `Tests/Ved/U2HierWireCheck.lean`（新） | 正例、15 の拒否対照、正の対照 2、実在行の形の拒否（lakefile と `ved.yml` に登録） |

register を持たない親の導出入力は H2a のまま `[conns]` で拒否する（`checkU2H` は変えていない）。

## 2. 仕組み

子の定理（`OutputsStmt`）は、範囲内の任意の入力 stream に対する出力を与える。H2a/H2b は stream を `insCIn cs ins`（各 port が親入力 `ins` を読む）に取った。H2c は
`netIn ck cs ins F`（data port は `F t port`、他は親入力）に取る。`F` は生成する閉じた定義で、`F t "_gen_x" = obs((arg ins).val t)`（`arg` は宣言の呼出し引数の閉項、`decl.ved_open_<名>_arg<j>_<k>`）。

生成する証明が供給するもの（kernel 検査。仮定ではない）:

- `hrange`: `F` は子の port の幅に収まる（signal の `isLt`）。
- `hrunF`（F2）: 閉じた run の各 cycle `t < K` で、port がつながる wire の値は `F t port`。`closed_run_asgOf`（その wire の assign を式に直す）と、入力 wire の値（`runHS_inputs`）と、検査で出す net の鎖（`netChain`、依存順）の範囲 `hlt` から、`simp` と `omega`。
- 結果の `srcOf ck g (netIn …) q t` は、`sig_of_obs_*` により宣言の呼出し `g (arg ins)` の観測に一致する。oracle（`Ow`）は `obs((g (arg ins)).val t)` で、H2b の `outputsOnHS_of_stepR`、`hstep`、deep の事実は変わらない。

net の値が宣言の引数と違えば `hrunF` が閉じず `[proof]` で拒否される（対照 1〜4）。

純 net: `x` が親 data 入力、または assign された wire で、その式の全読みが（再帰的に）純 net。register 出力、instance 出力、clock/reset、未駆動は純でない。

## 3. 範囲外（`[conns]` で拒否、理由を分類）

- **親 register 出力を読む instance 入力**（実在 14 行すべて）。宣言の呼出し引数が `Signal.loop` の束縛変数を含み（`hasLooseBVars`）、親入力 `ins` だけの閉項がない。H2b の方式（呼出しを自由 signal に抽象し、等式 `decl xs = open xs calls` を `rfl` で結ぶ）は、閉項でないと等式が成り立たない。次の 2 つが要る（どちらも本単位の範囲外）:
  (a) `Signal.loop` の oracle 付き展開定理（register の状態と oracle の同時帰納）。呼出しを関数変数 `G`（`g` 自体の抽象）にして `decl xs = open xs g` を `rfl` にし、DeepElab が `G s` を自由な組合せ関数の適用として reify できるように拡張する、でもよい。
  (b) 親全体を DeepElab に渡す: 合成が instance を返すので single-module 拒否（H2b の記録）。子を inline した平坦な証明は子の表そのものを reify するので、§4 の阻害が親に移る見込み（未測定）。
- 別 instance の出力を読む instance 入力（chained: IPv4、ICMP、ARP の checksum → byte）。
- 子の clock/reset を導出 net につなぐ（`[hier-shape]` の `clkRstOk`）。
- Bool の net（`e1 &&& e2` など）。net の評価の simp 集合が BitVec の演算（add、sub、and、or、xor、not、mux、定数）だけで、`Signal` の Bool 演算の値の補題が無い。`[proof]` で拒否（受理しない）。比較（`===`）も同様。
- 同じ子の複数 instance の対応付けは検査済み arrangement の順。間違えば `[proof]` で拒否（偽の受理は無い、偽の拒否はありうる）。合成が作る同一の重複 instance は、inlined net が等しければ同じ呼出しに対応づける（`wireShared` で確認）。

## 4. 子の葉は strict か（実測、a8f3b7d2 と同じ入口、scratch）

`#ved_u1 <child>` の結果。既定の制限:

| 子 | 最初の拒否 |
|---|---|
| HTTP.httpGetByte | `[proof]` simp の maxRecDepth |
| HTTP.httpRespByte | `[checker]` maxRecDepth |
| ARP.arpPacketByte | `[checker]` maxRecDepth |
| ICMP.icmpHeaderByte | `[proof]` unsolved goals |
| IPv4.ipv4HeaderChecksumSig | `[checker]` whnf の heartbeat 200000 |
| UsbWebServer.respByteMux | `[checker]` maxRecDepth |
| SHA512HW.kMux | `[checker]` maxRecDepth |

`maxRecDepth 200000`、`maxHeartbeats 2000000` に上げても 7 つとも拒否（353 秒、peak 7.9 GB）: httpGetByte unsolved goals、httpRespByte `simp` max steps、arpPacketByte / icmpHeaderByte / ipv4HeaderChecksumSig unsolved goals、respByteMux / kMux whnf timeout。
`#ved_u1_deep` は register のある module 用（組合せの子には `no registers`）。

## 5. 実在 14 行（`#ved_u2_hier`、scratch、H2c の入口）

14 行すべて `[conns]`（親 register 出力が子の入力、または register を含む式）。時間は 7.5〜10.5 秒、peak 2.0〜2.9 GB。H2b と同じ段階で、理由が分類されただけ（H2b は理由の区別なし）。
子の入力の駆動（抜粋）: R223/R224/R92/R220 = 計数 register `cnt` の出力そのもの（`burstEmit`）、R246 = 位相 register `phase` の出力、R193/R194 = `(cnt の下位 7 bit) - 1`（kMux）、R230〜R232 = `mux start 入力 latch`（入力と latch register の混合。latch register の D 入力と同じ net）、checksum の出力が byte child の入力（chained）、R210/R211/R227/R228 も latch register と入力の混合。

## 6. 対照（`Tests/Ved/U2HierWireCheck.lean`）

正例（型は入口の期待項と一致、標準 3 axioms、閉じた run が宣言の値に一致）: `wireAdd`（`accMod (a + b)`）、`wireTwo`（`acc2 (a + b) (a - b)`）、`wireShared`（定数 mask、let 共有 net、同じ子 2 instance と合成が作る重複 instance）、`wireMix`（導出と plain の混在、register 2 個）。

拒否対照（`checkU2HR` を実 synthesis の `(m, d)` の 1 箇所だけ変えて実行。段階と原因を検査し、環境全体が元と同じことを検査）:

| 対照 | 段階 |
|---|---|
| 1 instance の 2 wire の交換（`_gen_x`/`_gen_y`）、net が別の関数（add → sub）、net が別の入力を読む（b + a → b + b） | `[proof]` unsolved goals |
| port が plain 入力を読む（宣言の呼出しの形と合わない） | `[open]` no call of |
| 子の入力を親 register の出力に付け替える（1 cycle のずれ）、register の入力 net に付け替える | `[conns]` parent register output / not connected to a parent input |
| instance の自己ループ、net が自分の出力を読んで自分の入力に戻る、2 instance が net で互いを駆動 | `[order]` combinational cycle |
| 別 instance の出力を読む net（chained） | `[conns]` another instance's output |
| 子の clock / reset 接続を導出 net / data 入力に、data port を clock に | `[hier-shape]` clock/reset / width mismatch |
| 未駆動の名前を読む net | `[order]` undriven net |
| port を定数に | `[hier-shape]` plain wire reference |

正の対照: net wire の一貫した改名（受理）、本体の並べ替え（instance、assign、register の順。register 同士の相対順は slot 順なので保つ）（受理）。

実在行の形のコピー（子は小さな `accMod`/`acc2`）: 計数 register → 子（R223 の形）、register の式 → 子（R246/R210 の形）、latch と入力の混合 → 子 → 子（R230 の形）、chained、register なしの導出入力: すべて `[conns]`。

## 7. 回帰（各 `kjob lake build TARGET`）

Tests.Ved.U2HierRegCheck、U2HierCheck、U2HierPin、U2HierSemCheck、U1MultiRegCheck、H2OpenParentProbe、U1EntryCheck、U1HierCheck、U2HierWireCheck: すべて成功。

## 8. 未了と質問

- **質問 1**: register 出力を読む instance 入力（14 行すべて）は、§3 (a) の `Signal.loop` の oracle 展開（または DeepElab の自由関数適用）が要る。どちらを選ぶか（DeepElab の変更を許すか）。H2c の statement は変えずに済む見込みだが、未検証。
- **質問 2**: 子の葉が strict でなければ階層は成立しない（§4）。表の子（`kLut` / `Signal.mux` 連鎖の 18〜80 項目）を strict にするのは階層の外（`#ved_u1` の表の扱い）の仕事で、これを先に進めるか。
- Bool net と比較（`===`）の値の補題が無い（§3）。
