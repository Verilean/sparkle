# 残余の全コーパス測定と、再帰子の iota 規則化（D.D-4、Issue sparkle-ledger-dd4-res）

土台 feb02bdf（par/dres、3 回目の改訂）。**G-PRIM / TRUSTED は未承認。axiom・仮定・sorry・native_decide は入れていない。** 測定だけ。判断は reviewer。生データは KJOB_REPORT_PATH 側（`res3/s0..s3/raw/*`（per-file）、`res3/agg*.json|tsv`、`res3/probe/*`）。ソースツリーには置いていない。
測定の道具（すべて build ok）: `Tests/Gen5/PrimResidueLib.lean`（環境に依らない走査）、`scripts/gen5/prim_residue_dyn.sh`（ファイルごとに standalone で `lean` を実行して走査）、`scripts/gen5/prim_residue_agg.py`（集計）、`Tests/Gen5/IotaStudy.lean` と `scripts/gen5/iota_probe_batch.sh` / `iota_probe_agg.py`（iota の probe）、`scripts/gen5/lists/shard_*`（走査の対象ファイル一覧）。型の草案: `Tools/ShippingGen5IotaDraft.lean`（型だけ、定理なし）。

## 0. 最終の数（3 回目の改訂。以降の §1〜§2.5、§3 は 2 回目までの AllTests 環境の測定で、**この節が優先する**）

### 0.1 完了条件の範囲と分類

完了条件は「**全成功コンパイルの残余全件**」。「成功したコンパイル」の定義: 合成コマンド（`run.sh` と同じ grep: `#synthesizeVerilog` `#writeDesign` `#writeVerilogDesign` `#synthesizeVerilogDesign` `#synthesize ` `synthesizeCombinational` `synthesizeHierarchical`）を含む 496 ファイル（と target-only の 1 ファイル）を、**1 ファイルごとに別プロセスの `lean FILE`（SPARKLE_PROFILE=1、timeout 900）で実行し、終了コード 0 だったもの**（その中でコンパイラのプロファイルログに出た宣言が root）。環境を 1 つにまとめる必要がないので、AllTests と衝突するモジュール（`Tests.SynthesisTests`、`Tests.Synthesis.SynthCatalog` など）も測れた。

| 分類 | ファイル数 | 扱い | 根拠 |
|---|---|---|---|
| 実行が成功（rc 0）、AllTests の import 閉包の中 | 249 | **測った** | `Tests.AllTests` の import の推移的閉包（1253 モジュール）に含まれる |
| 実行が成功（rc 0）、閉包の外 | 219（target-only の `MemNameCollisionGenTest` 1 を含む） | **測った**（別環境にできない対象を含む。各ファイルが自分の環境） | 同上の閉包に入らないが standalone で成功した |
| target-only roots（`target_only_roots.txt` の 2 つ） | 2（`DesignTest` は 496 の中、`GenTest` は一覧に無く追加で実行。どちらも rc 0） | **測った** | `Tests.Compiler.MemNameCollisionGenTest` と `…DesignTest`。root は同名の 1 個（`SparkleMem.sync.4.8`）。残余は他に既にあるものに含まれ、定数は増えない |
| import する olean がない（`Tests/Gen5/*Check` 16 ファイル） | 16 | **範囲外** | 先頭行で失敗（`object file … does not exist`）。コンパイラは走っていない。合成コマンドの語は説明文・補題の文字列に出るだけで、lean_lib に build できる対象ではない |
| 実行が失敗（構文エラー、型エラー、`Cannot synthesise …`、検査の失敗、abort rc 134）| 13 | **範囲外** | コンパイルが成功していない。内訳: 構文エラー（`circuit` トークン 3。末尾が `unexpected token '#'` の 2 は、走査コマンドを末尾に足したことによる可能性があり原因は未調査）、型エラー 1（`Examples.VectorTest`）、`Cannot synthesise Sparkle.Core.runCircuitH: not inlinable`（`DeepElabReifyDemo`）、`omega` の失敗（`VerifyElabDemo`）、`Unknown identifier current`（`VerifyVerilog`、build 不通と同じ）、自分の検査の失敗（`SingleOutStaleProbe`、`ConeSharingPremises`）、abort（`ShippingMachineEntryTest` rc 134）、走査ライブラリ自身の再宣言（`PrimResidueLib`） |
| legacy ルートの成功経路 | 上の rc 0 のファイルの中 | **測った**（root として数えた、§0.2） | プロファイルログに legacy と出た宣言を root にした。legacy の root は 396 個（うち certified の印のない legacy だけの root 248） |

- ファイル総数 497（496 + target-only の `GenTest` 1）。rc 0 は 468、非成功 29（olean なし 16 + 失敗 13）。非成功 29 は**成功コンパイルでないので範囲外**で、その root は数えていない（走査が途中まで出した root があるファイルも数えない: `AGG_ALL=1` で数えると root 1402、定数 381 で、差は 33 root・2 定数）。
- 「root」= そのファイルの実行でコンパイラのプロファイルログに出た宣言（front-end の dispatch を過ぎたもの）＋そのファイル内の route 印付き / `@[hardware_module]` の定義。ログには**子の宣言・補助の定義も出る**（出力構造体の射影 `X.Out.field`、`match_1`、`List.brecOn` など。legacy だけの 248 個にそれが含まれる）ので、root 数は「モジュールのトップ」の数ではなく「コンパイラが処理した宣言」の数。

### 0.2 件数

| 項目 | 値 |
|---|---|
| 測定したファイル（= module）| **468**（rc 0、うち AllTests 閉包内 249、閉包外 219。target-only 2 を含む） |
| root（異なる宣言）| **1369**（certified front-end（S0 / mixed / machine / gate / design）の印を持つもの 1119、legacy だけ 248、印のみ 2） |
| 残余の定数（異なる）| **379** = コンストラクタ 190 + 型の基本形 177 + 再帰子 12 |
| ライブラリ（core / Sparkle.Core）| 142、ユーザー定義 237（宣言ごとの構造体、Tests / Examples / IP / local） |
| quot / opaque / extern / axiom | 0 |
| 再帰子 12 | `Bool.rec` `Decidable.rec` `Eq.rec` `Nat.rec` `False.rec` `Nat.le.rec` `BitVec.rec` `List.rec` `PSigma.rec` `Int.rec` `Prod.rec` + **`Sparkle.IP.BitNet.ArchMode.rec`（ユーザー定義、2 root、legacy だけの root）**。これまでの「ライブラリ 11」は閉じていなかった |
| 部分適用された残余 | `Signal`（902 箇所、全適用 41534）と `Prod.mk`（1 箇所）。再帰子の部分適用は 0 |
| 再帰子の箇所（主前提） | 3004 箇所すべて `bvar:def-parameter`（定義自身の仮引数）。コンストラクタの形の主前提は定義の中に出ない |
| 1 root あたりの残余 | 最小 2、中央値 71、最大 148 |

**範囲ごとの残余の和集合**: certified の root だけ 360（ctor 181 + type 168 + rec 11）。legacy だけの root 182（88 + 82 + 12）。AllTests 閉包内の root 354（176 + 166 + 12）。**legacy だけから来る定数 19**: `Append` `Append.mk` と `Sparkle.IP.BitNet.{ArchMode, ArchMode.HardwiredUnrolled, ArchMode.TimeMultiplexed, ArchMode.rec, LayerScales(.mk), LayerWeights(.mk), SoCConfig(.mk)}`、`Sparkle.IP.Net.{Ethernet.RxIn, TCP.TcpTxOut, UsbWebServer.TxSeqOut(.mk), UsbWebServer.WebServerOut(.mk)}`、`Tests.Compiler.SingleOutNestedRegressionTest.Two.mk`。**AllTests 閉包の外にしかない定数 25**（ほぼ宣言ごとの出力構造体 `XOut` とその `.mk`）。再帰子はこれらで 1 つだけ増える（`ArchMode.rec`）。

### 0.3 用途・型・Signal 存在行への影響

- **用途**: 残余の型の基本形は型（`Signal dom α`、`BitVec n`、`Decidable p`、`Eq …` など）、コンストラクタは値の構築（`Signal.mk`、`Bool.true` など）、再帰子は `if` / `match` / Nat・List の再帰・cast（`Eq.rec`）・矛盾（`False.rec`）。再帰子は root の本体に直接ではなくライブラリの補助定義（`casesOn` / `brecOn` / `ndrec` / `elim` など）の中だけに出る。
- **型**: 残余に型の基本形が 177 ある（`Signal` / `BitVec` など。`Signal` は全 root の 1310 に出て、部分適用がある唯一の残余）。`TDen` の `tcon` が `Signal dom`（1 引数）をどう扱うかに別の規則が要る。rank-2 の型抽象は 61 個（16 定義）で範囲外のまま。
- **Signal の存在行 `∃ v, CV env X sh.Ty v`**: 1 つでも残余の定数に行（または規則）がなければその root の存在行は払えない。root 1369 のうち**再帰子を 1 つも要さない root は 110**、残る 1259 は再帰子の行（または規則）が要る。root あたりの再帰子の必要数: `Bool.rec` 1252、`Decidable.rec` 1188、`Eq.rec` 1174、`Nat.rec` 1102、`False.rec` 1040、`Nat.le.rec` 1023、`BitVec.rec` 528、`List.rec` 421、`PSigma.rec` 386、`Int.rec` 58、`Prod.rec` 21、`ArchMode.rec` 2。定数ごとの到達 root 数が 3 以下の定数は 145 / 379（長い尾、ほとんどユーザー構造体）。**ユーザー構造体 237 は宣言ごとに行が要る**。
- 一覧（定数ごとの root 数・部分適用・全適用）は `res3/agg_consts.tsv`（379 行）。root ごとの route と残余の数は `res3/agg_roots.tsv`。以降の §3 の表は AllTests 環境の 336 定数のもの（その上位の行の数字は同じ傾向）。

### 0.4 iota の probe のやり直し（§4.2 の置き換え）

方法: AllTests 環境の machine 根 **129 個**を **5 個ずつ 26 バッチ**（各バッチ `timeout 900`、実測 81〜103 秒、全バッチ rc 0）。1 root あたりの fuel は**小さく 50000 ステップ**。fuel を使い切った root は**失敗として名前を出し、その root は数に入れない**（部分結果なし）。簡約器は草案の `unfold`（構文的 β）+ iota（主前提が構文的コンストラクタまたは Nat リテラルのとき）+ 構文的な射影 + **カーネルの Nat リテラル加速**（`Nat.add/sub/mul/div/mod/pow/gcd/land/lor/xor/shiftLeft/shiftRight/log2/succ`、`Nat.beq/ble/decEq/decLt/decLe`）で、結果は**異なる項ごと**（メモ化）の数。root の仮引数は束縛変数のまま（開いた項）。

| 項目 | 値 |
|---|---|
| root | 129 |
| fuel 内に終わった | **112** |
| fuel を使い切って失敗 | **17**（名前は下） |
| 終わった root のうち stuck の再帰子を持つもの | **112 / 112** |
| iota が発火した回数（終わった root の異なる項） | 185500: `Nat.rec` 177146、`List.rec` 6351、`Bool.rec` 1044、`Decidable.rec` 870、`PSigma.rec` 52、`BitVec.rec` 37 |
| Nat リテラル加速の回数 | 27885 |
| stuck の再帰子の箇所（主前提の形）| `const-app` 295400、`bvar` 68786、`proj` 5866 |

失敗の 17 root: `Sparkle.IP.Crypto.EcdsaSignDemo.{wMulN, wTx}`、`Sparkle.IP.Crypto.P256SignDemo.{wMul, wMulN}`、`Sparkle.IP.USB.Fido2Demo.wTx`、`Sparkle.IP.RV32.Divider.dividerSignal`、`Sparkle.Tests.Compiler.{MultiInstance.pe, ShippingDesignSVMemTest.memWide, ShippingMachineLinkedTest.callerLN, ShippingMachineLoopTest.{accLoop, divQ, loopPair}, ShippingMachineNormTest.{nConst, nMapNot, nSlice}, ShippingMachineRawTest.tupReg, ShippingMachineTeleTest.divInLoop}`。fuel 50000 では終わらなかったというだけで、**fuel を増やした再測定はしていない**（1 回目と 2 回目の probe は fuel 大で 20 分を超えた。fuel 1000000 で 3 root は 900 秒の timeout で打ち切られた。その結果は使っていない）。

読み方（**iota の健全性・関数性は未証明**。ここは構文的な簡約の測定だけ）:
- **iota は発火する**（185500 回。ほぼ `Nat.rec` で、Nat の幅の算術を構文展開した跡）。**しかし終わった 112 root のすべてに、iota で外れない再帰子の箇所が残る**。
- 残る箇所の主前提は 3 種: `const-app`（定数の適用で、構文的コンストラクタに簡約されないもの。例: 値が Signal 関数の結果や、リテラルに簡約できない `Decidable` のインスタンス）が 295400、`bvar`（λ に束縛された値、`if x then …`）が 68786、`proj` が 5866。**iota 規則は構文的コンストラクタにしか適用できず、bvar を主前提とする場合は止まる**ので、**再帰子の行は残す**。
- したがって「再帰子を iota 規則にして TRUSTED の候補を 2 クラスに減らす」とは言えない。減らすには `lam` の規則の設計変更（代入意味論など）が要るが、今回は調べていない。

---

(以下は 2 回目までの記録。数字は §0 に置き換えられたものがある)

## 1. 範囲（何を全件と呼ぶか）

- **環境**: `Tests.AllTests` を import した 1 つの環境（`kjob lake build Tests.AllTests` は 1688 job、13 分で成功）。IP/ と Examples/ のうち AllTests が import するモジュールを含む。
- **根（root）**: 環境の定義 `X` で、コンパイラの出力の印を持つもの。`X.machine_source`（machine ルート）、`X.gateValue`（gate ルート）、`X.gate_design*` / `X.machine_design*` / `X.design_*`（design ルート）。さらに `@[hardware_module]` 付きで印のないもの（`tagged`）。さらに corpus のスクリプト（`scripts/shipping-coverage/run.sh` と同じ grep: `#synthesizeVerilog` 他）が拾う 327 個の「合成コマンドの対象名」のうち、**自分のモジュールの定義に解決できた** 215 個（`synth`）。
- **残余**: 根から `defnInfo` を最大まで展開（定理が頭の適用は入らない）して、展開できない定数（コンストラクタ / 再帰子 / 型の基本形 / quot / opaque / axiom）が残余。前回の `PrimResidueCount` と同じ走査。型 `ci.type` は走査していない。
- **根の数**: 477（machine 129、gate 7、design 151、tagged 101、synth 215。複数のルートに入る根がある）。前回のサンプルは machine の 59。
- **「コンパイラが成功した」の代用**: 印の存在。`#synthesizeVerilog` が legacy ルートで成功しただけの宣言は印を持たないので、`synth`（名前が grep で拾え、定義に解決できたもの）で補った。**legacy ルートの成功そのものは測っていない**（プロファイルログが要る。run.sh 全体の再実行は重く、今回は行っていない）。
- **範囲外・未測定（正直に）**:
  1. 合成コマンドの名前 327 のうち **112 は根にできていない**: 109 は AllTests が import しないモジュール（`Tests.Synthesis.SynthCatalog` 29、`Tests.TestCompilerExtensions` 10、`Tests.SynthesisTests` 7 など 39 モジュール）、3 は import されているが名前が見つからない（局所定義）。
  2. 39 モジュールは同じ環境に入れられない（`Tests.SynthesisTests` が `test_hierarchical_alu` を `Tests.TestCircuits` と二重定義する等。`lake env lean` で import がエラー）。**モジュールごとの別環境**（AllTests + そのモジュール 1 つ）で測った（§2.5）。`Examples.HierarchicalCPU` は lean_lib に属さず build できない。`Tests.VerifyVerilog` は build が通らない（`Unknown identifier current`）ので、コンパイラが成功する対象ではない。
  3. target-only の root（`scripts/shipping-coverage/target_only_roots.txt` の 2 つ）は AllTests と同じ環境に入れられないので入っていない。
  4. 証明項を数えない近似は前回と同じ（`Eq.rec` などは証明由来のものを数えうる）。

## 2. 集計

### 2.1 残余の数（AllTests 環境、根 477）

| 分類 | 異なる定数 | うちライブラリ（core / Sparkle.Core） | うちユーザー定義 |
|---|---|---|---|
| コンストラクタ | 169 | 69 | 100 |
| 再帰子 | 11 | 11 | 0 |
| 型の基本形（inductive） | 156 | 60 | 96 |
| quot / opaque / extern / axiom | 0 | 0 | 0 |
| **計** | **336** | 140 | 196 |

- サンプル（59 宣言）の 153 からの増え方: ライブラリ分は 136 → 140（ほぼ頭打ち）、ユーザー構造体は 17 → 196。残余の増加は**ほぼすべて宣言ごとのユーザー構造体**で、ライブラリは有限。
- ルート別（異なる残余）: machine 169（ctor 84 / rec 11 / type 74）、gate 84（42 / 8 / 34）、design 171（85 / 11 / 75）、tagged 175（89 / 9 / 77）、synth 308（153 / 11 / 144）。ルートによって再帰子は 8〜11、**全 11 再帰子は machine と design ですでに出る**。
- 1 根あたりの残余: 最小 8、中央値 91、最大 148。

### 2.2 Signal の存在行 `∃ v, CV env X sh.Ty v` への影響

存在行は、根 `X` の展開の閉包に出る**残余の定数すべて**に表の行（または規則）が要る。1 つでも行がなければその根の存在行は払えない。表の「存在行が払えなくなる宣言数」はその定数を閉包に持つ根の数（= その定数の行がないときに払えなくなる根）。

- **全根が要る定数は 3 個**（`Nat`, `OfNat`（型）など）、**ほぼ全根（≥ 460）が要る定数は多数**: `Signal`（476）、`DomainConfig`（475）、`Bool`、`Nat.rec`（472）、`Bool.rec`（471）、`Decidable.rec`（471）、`Eq.rec`（470）、`False.rec`（468）。
- **再帰子を持たない根は 5 / 477**。つまり再帰子の行（または規則）がなければ、**ほぼすべて（472）の存在行が払えない**。再帰子 11 のうち `Nat.rec` / `Bool.rec` / `Decidable.rec` / `Eq.rec` / `False.rec` / `Nat.le.rec` は 455〜472 根、`BitVec.rec` 325、`List.rec` 301、`PSigma.rec` 218、`Int.rec` 26、`Prod.rec` 7。
- 「上位 k 個の定数の行だけで払える根の数」（頻度順）: 50 個で 1、100 個で 111、150 個で 286、200 個で 357、250 個で 415、300 個で 457、336 個で 477。**一部の行だけでは足りず、長い尾がある**（到達する根が 3 以下の定数が 130 個）。ユーザー構造体はほとんど 1 根専用。
- ユーザー定義の型・コンストラクタを 1 つも要しない根は 477 − 257 = 220、1 つ以上要する根は 257。
- **再帰子を定数ごとに見ると、再帰子は根のコードに直接は現れない**（§2.3）。ライブラリの補助定義（`casesOn` / `below` / `brecOn.go` / `ndrec` / `elim` / `fix.go`）の中の 16 箇所だけ。

### 2.3 再帰子の出現箇所（展開された 1737 個の異なる定義の中）

16 箇所 / 11 再帰子。すべてライブラリの補助定義で、**主前提（major）はその定義自身の仮引数（`bvar:def-parameter`）**。内訳: `Decidable.casesOn`, `Bool.casesOn`, `Eq.ndrec`, `BitVec.casesOn`, `Nat.below`, `Nat.brecOn.go`, `Nat.casesOn`, `List.below`, `List.casesOn`, `List.brecOn.go`, `Nat.le.casesOn`, `False.elim`, `WellFounded.Nat.fix.go`, `PSigma.casesOn`, `Int.casesOn`, `Prod.casesOn`。motive の宇宙: 15 箇所が宇宙パラメータ多相（`Sort u`）、1 箇所（`Nat.le.rec`）が Prop だけに除去（motive : … → Prop）。

### 2.4 部分適用の prim と rank-2

- **部分適用された残余**: 異なる残余で部分適用があるのは **`Sparkle.Core.Signal.Signal`（型の基本形）だけ**（3653 箇所、全適用は 106316 箇所）。`Signal dom`（`Functor (Signal dom)` のインスタンスの引数など）。**コンストラクタ・再帰子の部分適用は 0**。したがって η 展開の規則が要るのは `Signal dom` の型の部分適用だけで、`TDen` の `tcon` は `kinds` が 2 引数なので `Signal dom`（1 引数）に別の扱いが要る。
- **rank-2**（定義の値の中の型抽象 `fun (α : Type …) => …`、Sort / 型構成子を束縛する λ）: **定義の頭の λ 列（rank-1 の多相、spine の引数で消費）**: 265 個（180 定義）。**頭でない位置（本体の中・引数）**: 61 個（**16 定義**）。後者が rank-2 の候補で、草案は範囲外としている。16 定義の中身は未分類（機械的な近似: `Sort` で終わる型を束縛する λ。motive などの λ も入りうる）。

### 2.5 AllTests に入らないモジュール（モジュールごとの別環境）

モジュール別の別環境（AllTests + そのモジュール）で測れたもの: 35 / 36 モジュール（`Tests.SynthesisTests` は AllTests とも衝突して環境を作れず未測定）。新しい根の合計 91、それらの残余の和集合 168、AllTests 環境の残余に無い定数 23。

新しい定数の種別: {'type-former': 11, 'constructor': 12}。再帰子は増えない（11 のまま）。全体では 336 + 23 = 359 定数。

| モジュール | 新しい根 | 残余（異なる） | AllTests の残余に無い定数 |
|---|---|---|---|
| `Examples.CDC.MultiClockSim` | 2 | 92 | 0 |
| `IP.Arbiter.RoundRobin` | 1 | 78 | 0 |
| `IP.Bus.AXI4Lite.Master` | 1 | 80 | 0 |
| `IP.RV32.Bus` | 1 | 86 | 0 |
| `IP.RV32.CLINT` | 1 | 88 | 0 |
| `IP.RV32.CSR.File` | 1 | 99 | 0 |
| `IP.RV32.CSR.Supervisor` | 1 | 109 | 0 |
| `IP.RV32.MMU.Top` | 1 | 103 | 0 |
| `IP.RV32.Pipeline` | 1 | 119 | 0 |
| `IP.RV32.SoCVerilog` | 1 | 135 | 9 |
| `IP.RV32.Trap` | 1 | 109 | 0 |
| `IP.RV32.UART` | 1 | 103 | 0 |
| `IP.Video.H264.CAVLCSynth` | 1 | 105 | 0 |
| `IP.Video.H264.FrameEncoderSynth` | 1 | 105 | 0 |
| `IP.Video.H264.MP4EncoderSynth` | 1 | 105 | 0 |
| `IP.Video.H264.NALSynth` | 1 | 101 | 0 |
| `IP.Video.H264.QuantRoundtripSynth` | 1 | 101 | 0 |
| `IP.YOLOv8.ActivationBuffer` | 1 | 70 | 0 |
| `IP.YOLOv8.TextEmbedding` | 1 | 101 | 0 |
| `IP.YOLOv8.Top` | 2 | 101 | 0 |
| `Tests.Compiler.MultiOutputSubModuleHangRepro` | 4 | 103 | 2 |
| `Tests.CompilerTests` | 6 | 90 | 0 |
| `Tests.IP.Bus.CANHWTest` | 1 | 114 | 2 |
| `Tests.IP.Crypto.GHASHHWSynth` | 2 | 118 | 2 |
| `Tests.IP.Net.SLIPTest` | 2 | 97 | 4 |
| `Tests.IP.Net.UARTTest` | 2 | 122 | 0 |
| `Tests.IP.Net.UsbWebServerSynth` | 2 | 140 | 8 |
| `Tests.SymbolicParameterEmit` | 0 | 0 | 0 |
| `Tests.Synthesis.SynthCatalog` | 29 | 122 | 0 |
| `Tests.TestCompilerExtensions` | 10 | 104 | 0 |
| `Tests.TestConditionals` | 2 | 67 | 0 |
| `Tests.TestDRC` | 2 | 67 | 0 |
| `Tests.TestErrorDetection` | 3 | 68 | 0 |
| `Tests.TestUnbundle2` | 2 | 90 | 0 |
| `Tests.TupleProjectionTest` | 2 | 86 | 0 |

## 3. 残余の定数ごとの一覧

列: 型（`ci.type`、省略あり）、arity（完全適用に要る引数の数）、存在行が払えなくなる宣言数（= その定数を閉包に持つ根の数、477 中）、部分適用 / 全適用の箇所（展開された異なる定義の中）、例（根の 1 つ。`#ccp.c` は衛生名の根）。全行（336 定数）は `*.full.consts`（KJOB_REPORT_PATH）。

#### ライブラリ（core / Sparkle.Core）の型の基本形（inductive 型）: 60 定数

| 定数 | 型 | arity | 存在行が払えなくなる宣言数 | 部分適用 / 全適用の箇所 | 例 |
|---|---|---|---|---|---|
| `Nat` | Type | 0 | 477 | 0 / 0 | `#ccp.c` |
| `OfNat` | Type u → Nat → Type u | 2 | 477 | 0 / 1 | `#ccp.c` |
| `Sparkle.Core.Signal.Signal` | Sparkle.Core.Domain.DomainConfig → Type u → Type u | 2 | 476 | 3653 / 106316 | `#ccp.c` |
| `Sparkle.Core.Domain.DomainConfig` | Type | 0 | 475 | 0 / 0 | `#ccp.c` |
| `PProd` | Sort u → Sort v → Sort (max (max 1 u) v) | 2 | 472 | 0 / 8 | `#ccp.c` |
| `PUnit` | Sort u | 0 | 472 | 0 / 0 | `#ccp.c` |
| `Bool` | Type | 0 | 471 | 0 / 0 | `#ccp.c` |
| `Decidable` | Prop → Type | 1 | 471 | 0 / 20 | `#ccp.c` |
| `Eq` | {α : Sort u_1} → α → α → Prop | 3 | 471 | 0 / 83 | `#ccp.c` |
| `False` | Prop | 0 | 471 | 0 / 0 | `#ccp.c` |
| `LE` | Type u → Type u | 1 | 470 | 0 / 1 | `#ccp.c` |
| `LT` | Type u → Type u | 1 | 470 | 0 / 1 | `#ccp.c` |
| `Nat.le` | Nat → Nat → Prop | 2 | 470 | 0 / 10 | `#ccp.c` |
| `BitVec` | Nat → Type | 1 | 464 | 0 / 1301554 | `#ccp.c` |
| `HPow` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 458 | 0 / 1 | `#ccp.c` |
| `NatPow` | Type u → Type u | 1 | 458 | 0 / 2 | `#ccp.c` |
| `Pow` | Type u → Type v → Type (max u v) | 2 | 458 | 0 / 2 | `#ccp.c` |
| `HSub` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 456 | 0 / 1 | `#ccp.c` |
| `Sub` | Type u → Type u | 1 | 456 | 0 / 2 | `#ccp.c` |
| `HEq` | {α : Sort u} → α → {β : Sort u} → β → Prop | 4 | 455 | 0 / 3 | `#ccp.c` |
| `HMod` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 455 | 0 / 1 | `#ccp.c` |
| `Mod` | Type u → Type u | 1 | 455 | 0 / 2 | `#ccp.c` |
| `Fin` | Nat → Type | 1 | 452 | 0 / 19 | `#ccp.c` |
| `Functor` | (Type u → Type v) → Type (max (u + 1) v) | 1 | 450 | 0 / 1 | `#ccp.c` |
| `Add` | Type u → Type u | 1 | 445 | 0 / 2 | `#ccp.c` |
| `HAdd` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 445 | 0 / 1 | `#ccp.c` |
| `Applicative` | (Type u → Type v) → Type (max (u + 1) v) | 1 | 444 | 0 / 2 | `#ccp.c` |
| `Seq` | (Type u → Type v) → Type (max (u + 1) v) | 1 | 444 | 0 / 1 | `#ccp.c` |
| `Prod` | Type u → Type v → Type (max u v) | 2 | 349 | 0 / 2657 | `#ccp.c` |
| `Inhabited` | Sort u → Sort (max 1 u) | 1 | 348 | 0 / 6 | `#ccp.c` |
| `BEq` | Type u → Type u | 1 | 343 | 0 / 3 | `#ccp.c` |
| `List` | Type u → Type u | 1 | 301 | 0 / 91856 | `#ccp.c` |
| `Sparkle.Core.HListWireable` | List Type → Type | 1 | 300 | 0 / 2 | `#ccp.c` |
| `Sparkle.Core.HasDomain` | Type → outParam Sparkle.Core.Domain.DomainConfig → Type | 2 | 300 | 0 / 3 | `#ccp.c` |
| `Sparkle.Core.Wireable` | Type → Type | 1 | 300 | 0 / 1 | `#ccp.c` |
| `Div` | Type u → Type u | 1 | 242 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HDiv` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 242 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `PSigma` | {α : Sort u} → (α → Sort v) → Sort (max (max 1 u) v) | 2 | 218 | 0 / 20 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HOr` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 197 | 0 / 1 | `Sparkle.IP.Bus.AXI4Lite.Slave.axi4LiteSlave` |
| `HAnd` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 195 | 0 / 1 | `Sparkle.IP.Bus.AXI4Lite.Slave.axi4LiteSlave` |
| `HShiftRight` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 193 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `ShiftRight` | Type u → Type u | 1 | 193 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HMul` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 172 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `Mul` | Type u → Type u | 1 | 172 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `OrOp` | Type u → Type u | 1 | 164 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HShiftLeft` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 149 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `ShiftLeft` | Type u → Type u | 1 | 149 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `Complement` | Type u → Type u | 1 | 119 | 0 / 1 | `Sparkle.IP.Bus.AXI4Lite.Slave.axi4LiteSlave` |
| `HAppend` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 91 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HXor` | Type u → Type v → outParam (Type w) → Type (max (max u v) w) | 3 | 81 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `XorOp` | Type u → Type u | 1 | 81 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `AndOp` | Type u → Type u | 1 | 66 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `Neg` | Type u → Type u | 1 | 28 | 0 / 1 | `Sparkle.IP.RV32.aluSignal` |
| `Int` | Type | 0 | 26 | 0 / 0 | `Sparkle.IP.RV32.aluSignal` |
| `NatCast` | Type u → Type u | 1 | 26 | 0 / 2 | `Sparkle.IP.RV32.aluSignal` |
| `Int.NonNeg` | Int → Prop | 1 | 20 | 0 / 4 | `Sparkle.IP.RV32.aluSignal` |
| `Array` | Type u → Type u | 1 | 10 | 0 / 62 | `Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF` |
| `Bind` | (Type u → Type v) → Type (max (u + 1) v) | 1 | 6 | 0 / 1 | `Sparkle.Tests.RunCircuitHTest.counterH` |
| `Monad` | (Type u → Type v) → Type (max (u + 1) v) | 1 | 6 | 0 / 4 | `Sparkle.Tests.RunCircuitHTest.counterH` |
| `Pure` | (Type u → Type v) → Type (max (u + 1) v) | 1 | 6 | 0 / 1 | `Sparkle.Tests.RunCircuitHTest.counterH` |

#### ライブラリ（core / Sparkle.Core）のコンストラクタ: 69 定数

| 定数 | 型 | arity | 存在行が払えなくなる宣言数 | 部分適用 / 全適用の箇所 | 例 |
|---|---|---|---|---|---|
| `OfNat.mk` | {α : Type u} → {x : Nat} → α → OfNat α x | 3 | 477 | 0 / 3 | `#ccp.c` |
| `Sparkle.Core.Signal.Signal.mk` | {dom : Sparkle.Core.Domain.DomainConfig} → {α : Type u} → Sparkle.Cor… | 3 | 474 | 0 / 9 | `#ccp.c` |
| `Nat.succ` | Nat → Nat | 1 | 472 | 0 / 78 | `#ccp.c` |
| `Nat.zero` | Nat | 0 | 472 | 0 / 0 | `#ccp.c` |
| `PProd.mk` | {α : Sort u} → {β : Sort v} → α → β → α ×' β | 4 | 472 | 0 / 4 | `#ccp.c` |
| `PUnit.unit` | PUnit | 0 | 472 | 0 / 0 | `#ccp.c` |
| `Bool.false` | Bool | 0 | 471 | 0 / 0 | `#ccp.c` |
| `Bool.true` | Bool | 0 | 471 | 0 / 0 | `#ccp.c` |
| `Decidable.isFalse` | {p : Prop} → ¬p → Decidable p | 2 | 471 | 0 / 9 | `#ccp.c` |
| `Decidable.isTrue` | {p : Prop} → p → Decidable p | 2 | 471 | 0 / 9 | `#ccp.c` |
| `Eq.refl` | ∀ {α : Sort u_1} (a : α), a = a | 2 | 471 | 0 / 5 | `#ccp.c` |
| `LE.mk` | {α : Type u} → (α → α → Prop) → LE α | 2 | 470 | 0 / 2 | `#ccp.c` |
| `LT.mk` | {α : Type u} → (α → α → Prop) → LT α | 2 | 470 | 0 / 2 | `#ccp.c` |
| `HPow.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 458 | 0 / 1 | `#ccp.c` |
| `NatPow.mk` | {α : Type u} → (α → Nat → α) → NatPow α | 2 | 458 | 0 / 2 | `#ccp.c` |
| `Pow.mk` | {α : Type u} → {β : Type v} → (α → β → α) → Pow α β | 3 | 458 | 0 / 1 | `#ccp.c` |
| `BitVec.ofFin` | {w : Nat} → Fin (2 ^ w) → BitVec w | 2 | 456 | 0 / 12 | `#ccp.c` |
| `HSub.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 456 | 0 / 2 | `#ccp.c` |
| `Sub.mk` | {α : Type u} → (α → α → α) → Sub α | 2 | 456 | 0 / 3 | `#ccp.c` |
| `Fin.mk` | {n : Nat} → (val : Nat) → val < n → Fin n | 3 | 455 | 0 / 2 | `#ccp.c` |
| `HEq.refl` | ∀ {α : Sort u} (a : α), a ≍ a | 2 | 455 | 0 / 1 | `#ccp.c` |
| `HMod.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 455 | 0 / 1 | `#ccp.c` |
| `Mod.mk` | {α : Type u} → (α → α → α) → Mod α | 2 | 455 | 0 / 2 | `#ccp.c` |
| `Nat.le.refl` | ∀ {n : Nat}, n.le n | 1 | 455 | 0 / 2 | `#ccp.c` |
| `Nat.le.step` | ∀ {n m : Nat}, n.le m → n.le m.succ | 3 | 455 | 0 / 2 | `#ccp.c` |
| `Functor.mk` | {f : Type u → Type v} → ({α β : Type u} → (α → β) → f α → f β) → ({α … | 3 | 450 | 0 / 2 | `#ccp.c` |
| `Add.mk` | {α : Type u} → (α → α → α) → Add α | 2 | 445 | 0 / 3 | `#ccp.c` |
| `HAdd.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 445 | 0 / 3 | `#ccp.c` |
| `Applicative.mk` | {f : Type u → Type v} → [toFunctor : Functor f] → [toPure : Pure f] →… | 6 | 444 | 0 / 2 | `#ccp.c` |
| `Pure.mk` | {f : Type u → Type v} → ({α : Type u} → α → f α) → Pure f | 2 | 444 | 0 / 2 | `#ccp.c` |
| `Seq.mk` | {f : Type u → Type v} → ({α β : Type u} → f (α → β) → (Unit → f α) → … | 2 | 444 | 0 / 2 | `#ccp.c` |
| `SeqLeft.mk` | {f : Type u → Type v} → ({α β : Type u} → f α → (Unit → f β) → f α) →… | 2 | 444 | 0 / 2 | `#ccp.c` |
| `SeqRight.mk` | {f : Type u → Type v} → ({α β : Type u} → f α → (Unit → f β) → f β) →… | 2 | 444 | 0 / 2 | `#ccp.c` |
| `Inhabited.mk` | {α : Sort u} → α → Inhabited α | 2 | 348 | 0 / 15 | `#ccp.c` |
| `Prod.mk` | {α : Type u} → {β : Type v} → α → β → α × β | 4 | 346 | 0 / 981 | `#ccp.c` |
| `BEq.mk` | {α : Type u} → (α → α → Bool) → BEq α | 2 | 343 | 0 / 1 | `#ccp.c` |
| `Sparkle.Core.Domain.ActiveEdge.rising` | Sparkle.Core.Domain.ActiveEdge | 0 | 323 | 0 / 0 | `SimNamesTestA.snDup` |
| `Sparkle.Core.Domain.DomainConfig.mk` | Nat → Sparkle.Core.Domain.ActiveEdge → Sparkle.Core.Domain.ResetKind … | 3 | 323 | 0 / 1 | `SimNamesTestA.snDup` |
| `Sparkle.IR.Type.ResetKind.synchronous` | Sparkle.IR.Type.ResetKind | 0 | 323 | 0 / 0 | `SimNamesTestA.snDup` |
| `List.cons` | {α : Type u} → α → List α → List α | 3 | 301 | 0 / 1240341 | `#ccp.c` |
| `List.nil` | {α : Type u} → List α | 1 | 301 | 0 / 53130 | `#ccp.c` |
| `Sparkle.Core.HListWireable.mk` | {αs : List Type} → Sparkle.Core.HListWireable αs | 1 | 300 | 0 / 2 | `#ccp.c` |
| `Sparkle.Core.HasDomain.mk` | {ρ : Type} → {dom : outParam Sparkle.Core.Domain.DomainConfig} → Spar… | 2 | 300 | 0 / 84 | `#ccp.c` |
| `Sparkle.Core.Wireable.mk` | {α : Type} → Nat → Sparkle.Core.Wireable α | 2 | 300 | 0 / 2 | `#ccp.c` |
| `Div.mk` | {α : Type u} → (α → α → α) → Div α | 2 | 242 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HDiv.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 242 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `PSigma.mk` | {α : Sort u} → {β : α → Sort v} → (fst : α) → β fst → PSigma β | 4 | 218 | 0 / 4 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HOr.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 197 | 0 / 3 | `Sparkle.IP.Bus.AXI4Lite.Slave.axi4LiteSlave` |
| `HAnd.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 195 | 0 / 3 | `Sparkle.IP.Bus.AXI4Lite.Slave.axi4LiteSlave` |
| `HShiftRight.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 193 | 0 / 6 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `ShiftRight.mk` | {α : Type u} → (α → α → α) → ShiftRight α | 2 | 193 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HMul.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 172 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `Mul.mk` | {α : Type u} → (α → α → α) → Mul α | 2 | 172 | 0 / 3 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `OrOp.mk` | {α : Type u} → (α → α → α) → OrOp α | 2 | 164 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HShiftLeft.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 149 | 0 / 5 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `ShiftLeft.mk` | {α : Type u} → (α → α → α) → ShiftLeft α | 2 | 149 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `Complement.mk` | {α : Type u} → (α → α) → Complement α | 2 | 119 | 0 / 3 | `Sparkle.IP.Bus.AXI4Lite.Slave.axi4LiteSlave` |
| `HAppend.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 91 | 0 / 4 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `HXor.mk` | {α : Type u} → {β : Type v} → {γ : outParam (Type w)} → (α → β → γ) →… | 4 | 81 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `XorOp.mk` | {α : Type u} → (α → α → α) → XorOp α | 2 | 81 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `AndOp.mk` | {α : Type u} → (α → α → α) → AndOp α | 2 | 66 | 0 / 2 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `Neg.mk` | {α : Type u} → (α → α) → Neg α | 2 | 28 | 0 / 3 | `Sparkle.IP.RV32.aluSignal` |
| `Int.negSucc` | Nat → Int | 1 | 26 | 0 / 28 | `Sparkle.IP.RV32.aluSignal` |
| `Int.ofNat` | Nat → Int | 1 | 26 | 0 / 33 | `Sparkle.IP.RV32.aluSignal` |
| `NatCast.mk` | {R : Type u} → (Nat → R) → NatCast R | 2 | 26 | 0 / 1 | `Sparkle.IP.RV32.aluSignal` |
| `Int.NonNeg.mk` | ∀ (n : Nat), (Int.ofNat n).NonNeg | 1 | 20 | 0 / 1 | `Sparkle.IP.RV32.aluSignal` |
| `Array.mk` | {α : Type u} → List α → Array α | 2 | 10 | 0 / 1 | `Sparkle.IP.Crypto.Keccak256Sponge.wKeccakF` |
| `Bind.mk` | {m : Type u → Type v} → ({α β : Type u} → m α → (α → m β) → m β) → Bi… | 2 | 6 | 0 / 1 | `Sparkle.Tests.RunCircuitHTest.counterH` |
| `Monad.mk` | {m : Type u → Type v} → [toApplicative : Applicative m] → [toBind : B… | 3 | 6 | 0 / 1 | `Sparkle.Tests.RunCircuitHTest.counterH` |

#### ライブラリ（core / Sparkle.Core）の再帰子: 11 定数

| 定数 | 型 | arity | 存在行が払えなくなる宣言数 | 部分適用 / 全適用の箇所 | 例 |
|---|---|---|---|---|---|
| `Nat.rec` | {motive : Nat → Sort u} → motive Nat.zero → ((n : Nat) → motive n → m… | 4 | 472 | 0 / 4 | `#ccp.c` |
| `Bool.rec` | {motive : Bool → Sort u} → motive false → motive true → (t : Bool) → … | 4 | 471 | 0 / 1 | `#ccp.c` |
| `Decidable.rec` | {p : Prop} → {motive : Decidable p → Sort u} → ((h : ¬p) → motive (is… | 5 | 471 | 0 / 1 | `#ccp.c` |
| `Eq.rec` | {α : Sort u_1} → {a : α} → {motive : (a_1 : α) → a = a_1 → Sort u} → … | 6 | 470 | 0 / 1 | `#ccp.c` |
| `False.rec` | (motive : False → Sort u) → (t : False) → motive t | 2 | 468 | 0 / 1 | `#ccp.c` |
| `Nat.le.rec` | ∀ {n : Nat} {motive : (a : Nat) → n.le a → Prop}, motive n ⋯ → (∀ {m … | 6 | 455 | 0 / 1 | `#ccp.c` |
| `BitVec.rec` | {w : Nat} → {motive : BitVec w → Sort u} → ((toFin : Fin (2 ^ w)) → m… | 4 | 325 | 0 / 1 | `#ccp.c` |
| `List.rec` | {α : Type u} → {motive : List α → Sort u_1} → motive [] → ((head : α)… | 5 | 301 | 0 / 3 | `#ccp.c` |
| `PSigma.rec` | {α : Sort u} → {β : α → Sort v} → {motive : PSigma β → Sort u_1} → ((… | 5 | 218 | 0 / 1 | `Sparkle.IP.Bus.LINHW.checksumHW` |
| `Int.rec` | {motive : Int → Sort u} → ((a : Nat) → motive (Int.ofNat a)) → ((a : … | 4 | 26 | 0 / 1 | `Sparkle.IP.RV32.aluSignal` |
| `Prod.rec` | {α : Type u} → {β : Type v} → {motive : α × β → Sort u_1} → ((fst : α… | 5 | 7 | 0 / 1 | `Sparkle.IP.YOLOv8.Blocks.ConvBnSiLU.convBnSiLU` |

#### ユーザー定義（Tests / Examples / IP / local）の型・コンストラクタ: 196 定数（宣言ごとの構造体。表は上位 25 と集計）

種別: type-former 96, constructor 100

| 定数 | 種別 | 型 | 存在行が払えなくなる宣言数 | モジュール |
|---|---|---|---|---|
| `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 33 | `Tests.Compiler.ShippingChildBoundaryTest` |
| `Sparkle.Tests.Compiler.ShippingChildBoundaryTest.AccOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 33 | `Tests.Compiler.ShippingChildBoundaryTest` |
| `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 22 | `Tests.Compiler.ShippingMachineSeqTest` |
| `Sparkle.Tests.Compiler.ShippingMachineSeqTest.CntOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 22 | `Tests.Compiler.ShippingMachineSeqTest` |
| `Sparkle.IP.Crypto.ModInvHW.ModInvOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 18 | `IP.Crypto.ModInvHW` |
| `Sparkle.IP.Crypto.ModInvHW.ModInvOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 18 | `IP.Crypto.ModInvHW` |
| `Sparkle.IP.Crypto.Secp256k1ECDSAHW.SignOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 13 | `IP.Crypto.Secp256k1ECDSAHW` |
| `Sparkle.IP.Crypto.Secp256k1ECDSAHW.SignOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 13 | `IP.Crypto.Secp256k1ECDSAHW` |
| `Sparkle.IP.Crypto.Secp256k1PointOpHW.PointOpOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 13 | `IP.Crypto.Secp256k1PointOpHW` |
| `Sparkle.IP.Crypto.Secp256k1PointOpHW.PointOpOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 13 | `IP.Crypto.Secp256k1PointOpHW` |
| `Sparkle.IP.Crypto.Secp256k1ScalarMulHW.ScalarMulOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 13 | `IP.Crypto.Secp256k1ScalarMulHW` |
| `Sparkle.IP.Crypto.Secp256k1ScalarMulHW.ScalarMulOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 13 | `IP.Crypto.Secp256k1ScalarMulHW` |
| `Sparkle.IP.Crypto.Secp256k1FieldHW.MulOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 12 | `IP.Crypto.Secp256k1FieldHW` |
| `Sparkle.IP.Crypto.Secp256k1FieldHW.MulOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 12 | `IP.Crypto.Secp256k1FieldHW` |
| `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 12 | `IP.Crypto.Secp256k1OrderHW` |
| `Sparkle.IP.Crypto.Secp256k1OrderHW.MulOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 12 | `IP.Crypto.Secp256k1OrderHW` |
| `Sparkle.IP.Crypto.EcdsaSignDemo.SignCoreOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 9 | `IP.Crypto.EcdsaSignDemo` |
| `Sparkle.IP.Crypto.EcdsaSignDemo.SignCoreOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 9 | `IP.Crypto.EcdsaSignDemo` |
| `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 9 | `IP.Crypto.Keccak256HW` |
| `Sparkle.IP.Crypto.Keccak256HW.KeccakFOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 9 | `IP.Crypto.Keccak256HW` |
| `Sparkle.IP.Net.UART.RxOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 9 | `IP.Net.UART` |
| `Sparkle.IP.Net.UART.RxOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 9 | `IP.Net.UART` |
| `Sparkle.IP.Net.UART.TxOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 9 | `IP.Net.UART` |
| `Sparkle.IP.Net.UART.TxOut.mk` | constructor | {dom : Sparkle.Core.Domain.DomainConfig} → Sparkle.Core.Sig… | 9 | `IP.Net.UART` |
| `Sparkle.IP.Crypto.HMACSHA512HW.HmacOut` | type-former | Sparkle.Core.Domain.DomainConfig → Type | 8 | `IP.Crypto.HMACSHA512HW` |

ユーザー定義 196 定数のうち、到達する宣言が 1 つだけのもの: 49、3 つ以下: 130、最大 33。


## 4. 再帰子を `RecursorVal.rules` の iota 規則として書けるか

型の草案: `Tools/ShippingGen5IotaDraft.lean`（型だけ。build ok）。データの確認: `Tests/Gen5/IotaStudy.lean`（`#iota_study`）。

### 4.1 規則の草案

`RecursorVal` は `numParams / numMotives / numMinors / numIndices / k / rules`（`RecursorRule := ⟨ctor, nfields, rhs⟩`）を持つ。主前提が `rule.ctor` のコンストラクタ適用なら、
`rec ls params motives minors indices (C params fields) extra  ⟶  (rule.rhs.instantiateLevelParams ls).beta (params ++ motives ++ minors ++ fields) extra`。
これは `unfold` と同じく **spine 全体の構文的な書き換え**で、新しい `CVE` の規則は 1 つ:

```lean
-- Tools/ShippingGen5IotaDraft.lean より（型のみ）
inductive IotaStep (env : Environment) : Expr → Expr → Prop
  | step {rv ls args sp rule cls}
      (hrv : env.find? rv.name = some (.recInfo rv)) (hsp : RecSpine.split rv args = some sp)
      (hrule : rule ∈ rv.rules) (hctor : sp.major.getAppFn = .const rule.ctor cls)
      (hfields : sp.major.getAppNumArgs = rv.numParams + rule.nfields) :
      IotaStep env (mkAppN (.const rv.name ls) args)
        (mkAppN ((rule.rhs.instantiateLevelParams rv.levelParams ls).beta (sp.params ++ sp.motives ++ sp.minors ++ fields)) sp.extra)
-- CVE に足す規則（草案）:  | iota (hs : IotaStep env e e') (h : CVE PT env ρ e' τ α v) : CVE PT env ρ e τ α v
```

- **排他**: 頭が `recInfo` の spine だけに適用でき、`unfold`（`defnInfo`）・`prim`（非 `defnInfo` で表に行がある）・`app`（頭が const でない）と重ならない。再帰子は表に行を持たない（`PT.tms` の `recur` の行は規則が使わない）。
- **motive が `Sort u` を取る問題**: motive は**値にならず構文の中にとどまる**（`rule.rhs` への代入と β で消える）。したがって `Dyn`（`Type 0`）にも `TDen` にも入らない。規則は宇宙に依らない。行（`TmRow.den : List Arg → Option Dyn`）として書く場合は、motive が `T → Type`（`Type 1`）になり `Arg` に `Type 1` の枝が要り、結果の型 `motive m : Type` は u = 1 のときだけ `Dyn` に入る（u ≥ 2 は入らない。u = 0 は証明で値ではない）。**規則（iota）なら宇宙の制約は出ない。これは行より有利**。
- **`Type 0` の `Dyn` の制約**: 規則の結論は `CVE ρ e τ α v` で、`τ α v` は還元後の項の導出が決める。再帰子の宇宙を直接表さないので、Type 0 の制約は **還元後の項が Type 0 の値かどうか**だけになる。これは unfold と同じ。
- **ストラクチャ eta / `k`-like**（`Eq.rec`, `HEq.rec` は `k = true`）: `Eq.rec` の主前提は証明 `h : a = b`。`k` 規則は `h` が `Eq.refl` の形でなくても（`a ≡ b` なら）還元する。構文的な `ctor` の一致では書けない。`Eq.rec` / `Eq.ndrec` は残余に出るが、値としては**型の等式による cast**で、`cast` を使う項が型 `T` の値を `T'` として返す。`a ≡ b` の判定（定義的等価）を規則が持たなければ iota は発火しない。→ `Eq.rec` / `False.rec` / `Nat.le.rec`（Prop への除去）は**証明由来**で、値の意味にとっては別の扱い（証明無関係）が自然で、iota の対象にしない案が妥当。
- **Nat リテラル**: 主前提が `lit n` のとき規則は `Nat.zero` / `Nat.succ (lit (n−1))` に変換する必要がある（カーネルの規則）。さらに `Nat.add` / `Nat.pow` などは**カーネルの GMP 加速**なしでは `Nat.rec` の単項展開になる（§4.2）。

### 4.2 （2 回目までの結論。§0.4 が置き換える）

2 回目までの probe は「machine 根 30 個・fuel 400000 で 30 / 30 が fuel 切れ」で、数は傾向にとどまっていた。**数値は §0.4（129 root・fuel 50000・失敗は名前を出して数に入れない）に置き換えた**。結論（構文的 iota は主前提が構文的コンストラクタの場合だけ、bvar を主前提とする箇所で止まる、再帰子の行は残す）は §0.4 でも変わらない。以下の手順の説明（4.1 と、Nat リテラルの加速が要る理由、別設計の候補）は参考として残す。

### 4.3 書けた場合の残余の数（参考）

もし再帰子が規則で完全に置き換えられたとすると、AllTests 環境の残余は 336 − 11 = **325**（コンストラクタ 169 + 型の基本形 156）、そのうちライブラリは 69 + 60 = **129**、ユーザー定義が 196。サンプルの 153 − 11 = 142 に対応する。だが §4.2 のとおり、**この前提は成り立たない**ので、この数は上限の参考値にとどまる。

## 5. 結論

1. **残余の全件**（§0）: 全成功コンパイル（497 ファイルのうち rc 0 の 468、root 1369）の残余は 379 定数 = コンストラクタ 190 + 型の基本形 177 + 再帰子 12。ライブラリ由来 142（ほぼ閉じている）、ユーザー構造体由来 237（宣言ごとに増える）。非成功 29 ファイルは範囲外（理由は §0.1）。
2. **存在行への影響**: root 1369 のうち 1259 が再帰子の行を要する（再帰子を要さない root は 110）。再帰子の行（または規則）が決定的。型・コンストラクタはユーザー構造体が長い尾（3 root 以下の定数が 145）を作る。
3. **部分適用の prim**: `Signal`（902 箇所）と `Prod.mk`（1 箇所）。再帰子の部分適用は 0。rank-2 の型抽象は 61 個（16 定義）で範囲外。
4. **再帰子の iota 規則**: 構文的な規則は書ける（型の草案）。129 root の probe で iota は発火する（185500 回）が、**終わった 112 root のすべてに stuck の再帰子が残る**（bvar 68786、const-app 295400、proj 5866）。17 root は fuel 50000 で終わらず、名前を §0.4 に出した。**iota は構文的 constructor にしか適用できず、bvar を主前提とする場合は止まる。よって再帰子の行は残す**。iota の健全性・関数性は未証明。
5. **G-PRIM / TRUSTED は未承認**。判断は reviewer。材料: (a) 再帰子の行は ConstantInfo から一様に機械生成できるが、名前の対応が信頼の対象、(b) ユーザー構造体 237 は宣言ごとに行が要る（生成は機械的）、(c) iota で外せる再帰子は一部で、全 root に stuck が残る。

## 6. 主張しないこと

- 範囲外にした 29 ファイル（olean なし 16、失敗 13）のコンパイル。
- fuel 50000 で終わらなかった 17 root の iota 簡約の結果。
- iota の規則の健全性・関数性（未証明。型の草案だけ）。
- 新しい TRUSTED の採用・必要性、G-PRIM の判断。台帳の数の変更（FG 75 / T1 57 のまま。今回 FG -0 +0 / T1 -0 +0）。
- 証明項を数えない近似（`Eq.rec` などは証明由来のものを数えうる）は §1 と同じ。
