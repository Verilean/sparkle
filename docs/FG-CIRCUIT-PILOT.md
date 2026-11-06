# FG 回路の核 S1 パイロット（Issue `sparkle-fg-circuit-pilot`）

土台 `ff3d31c6`（par/fgc）。戦略: `docs/FG-CIRCUIT-STRATEGY-2026-11-06.md` §4–§7。S1 は方式の検証であり、**FG の完了ではない**（台帳 FG 75 / T1 57、今回 FG -0 +0 / T1 -0 +0）。
追加ファイル: `Tools/ShippingFGCircuit.lean`、`Tools/ShippingFGCircuitRoots.lean`、`Tests/Gen5/FGCircuitPilotCheck.lean`、本書。既存ファイルは書き換えていない（lakefile への追記のみ、最初の commit で 1 回）。
新しい TRUSTED・axiom・sorry・native_decide はない（`#print axioms` は全て `propext, Classical.choice, Quot.sound`）。

## 1. 結論の型（先に固定）

概念上の形:

```
compileCircuit env source params = .ok artifact
  → ∃ sourceMeaning, SourceDenotes env source params sourceMeaning ∧ HasConcretePackage artifact ∧ ObservationsEqual sourceMeaning artifact
```

Lean での対応（`Tools/ShippingFGCircuit.lean`）:

| 概念 | Lean | 既存の FG 型との対応 |
|---|---|---|
| `compileCircuit … = .ok artifact` | `EntryWitness ReflectsAll L declName parameters mctx cctx w w' b D`（`artifact = (b, D)`、`env = envAt cref w`） | `FGLedgerPremisesStmtH` の外側の前提そのもの（新しい仮定なし） |
| `SourceDenotes env X params sh m` | `params = [] ∧ ∃ ci, env.find? X = some ci ∧ shapeOf ci = some sh ∧ CircCV env X sh.Ty m`（定義域が固定された宣言には `SourceDenotesMono`） | `DeclConnect` の `CV env X sh.Ty v`。**`CV` を binder から具体的な `CircCV` に置き換えた** |
| `HasConcretePackage` | `p.decl = declName ∧ TopShips p n declName b raw D` | H の第 3 連言 `TopShips`（全入力列・全 `T`、clk/rst は `b` の入力として扱う既存契約） |
| `ObservationsEqual sh m p` | `ShapeMatches sh p.d p.kD ∧ ∀ i bools bits, sh.obs m i bools bits = p.src i bools bits`（定義域固定: `ObservationsEqualMono`、位置は 0 から） | `DeclConnect` の `ShapeMatches` と `ObsC` |
| 全体 | `FGCircuitConclusion env P Post declName parameters b D` | H の結論の後半（`∃ raw, Post` と `P declName = some p` と `TopShips`）に `SourceDenotes`/`ObservationsEqual` を同じ `p` で束ねたもの |
| 対応定理 | `fgCircuit_of_H : FGLedgerPremisesStmtH → … → FGCircuitConclusion …`（H は未証明。参考部品）（`genP_decl` で `p.decl = declName`、`declConnect_mono` で `TgtRun` から top へ） | H から S1 の結論が出る。追加の前提は `parameters = []` のみ |

`SourceDenotes` は生成出力・package・IR から定義していない。引数に `Pkg` も `Module` もない（`Tests/Gen5/FGCircuitPilotCheck.lean` の `rfl` 照合）。元ソースの宣言の値の `Expr` を、Signal/BitVec の適用単位の意味 `CD`（§3）で読んだ値が意味である。
clock / reset: `TopShips` の既存契約（`clk`/`rst` が `b` の入力にあれば全時刻 0、レジスタは reset 値 `f.init` から開始）。**reset を assert した挙動は S1 の主張に含まれない**（ソースの `Signal.register` に reset がないため、IR の reset 分岐は意味の外）。

## 2. 部品の出所（SHA）

| 部品 | 出所 | 使い方 |
|---|---|---|
| `Dyn` / `Entry` / `Val` | par/dd4-int `fe106963` の `Tools/ShippingGen5ConstValueE.lean`（変更なし） | `CD` の環境の型だけ。**ConstValueEKey/ES/ESProof/EV など他の 7 ファイルは持ち込んだが未使用**（下記の理由）。 |
| 組立 | `5e5c9bd2`（土台に含まれる）、`SM1`（H） | `fgCircuit_of_H` の入力（H）としてだけ使う |
| 3 root の測定 | `e37da005` §Trace | 3 root の選択と「停止して再帰子 0」の確認（`Signal.*`/`BitVec.*` を展開しない） |
| 宣言ごとの端点 | 既存の `#machine_endpoint`（`Tools/ShippingMachineCommand.lean`） | 既存の reader/genData → IR の経路。各 root で `X.machine_sound` / `X.machine_ships_wired` を生成（kernel の `Eq.refl` 検査） |
| Q-B shard / Q-C | 未使用（`d4shard 20772d29` / `d4qc 3616089c`）| 今回の 4 root は shard を要しない |

**CVEKV を使わなかった理由（実測した事実）**: `CVEKVB.prim` と `TDenV.tcon` は `¬ IsDefn env c` を要求するので、`Signal.register` / `Signal.loop` / `Signal.mux` / `BitVec.ofNat`（すべて `defnInfo`）を「停止する prim」にできず、`unfold` すると `Signal.loop` が `loopGo`（整礎再帰）に入る。また `HAdd.hAdd` は射影関数（`defnInfo`）で、`unfold` すると値が `Expr.proj` になるが `CVEKV` に `proj` の規則がない（規則一覧を読んだ結果。導出を実際に試したのではない）。したがって e37da005 の「停止 7 key」は今の `CVEKV` の規則では導出できない。パイロットは、**適用単位の規則**（定数・level・引数すべてを 1 規則で認識する）を持つ小さい関係 `CD`/`TD` を新設した。`CVEKV` の関数性・弱化の証明は流用していない（`CD` の関数性は未証明、§6）。

## 3. 具体化した primitive（適用の単位）

`CD ρ e α v`: 式 `e` が Lean の値 `v : α` を意味する（`Type 0` のみ）。型は `TD`。規則は 1 つの完全な適用に 1 つ。値は**同じ Lean 定数**で作る（IR からではない）。表の行だけでは意味を与えたことにならないので、各行に証明を付けた（`primTable`、`Check` で「各証明が存在し標準 axiom のみ」を検査）。

| 宣言 / level | 引数 | 結果型 | 値の意味 | IR 演算 | 時相・reset | 証明 |
|---|---|---|---|---|---|---|
| `OfNat.ofNat.{0}` | `Nat, lit n, instOfNatNat n` | `Nat` | `n` | なし（静的） | 静的 | 規則 `natLit` |
| `BitVec.ofNat` | `w, n` | `BitVec w` | `BitVec.ofNat w n` | `Expr.const n w` | 静的 | `ir_const_agrees`（IR の `evalExpr (.const n w) = (BitVec.ofNat w n).toNat`） |
| `Signal.pure.{0}` | `dom, T, a` | `Signal dom T` | 全時刻 `a` | const/ref | 全 cycle 同値 | `pure_val`、`ir_const_agrees` |
| `Signal.register.{0}` | `dom, T, init, s` | `Signal dom T` | `t=0: init`、`t+1: s t` | `Stmt.register out clk (rst,k) in init` | cycle t ↔ IR cycle t。`rst` は 0 に固定（`TopShips`）。開始値は slot の init | `register_val_zero`、`register_val_succ`、`ir_register_step_rst0`、`ir_register_reset_value` |
| `Signal.mux.{0}` | `dom, T, c, a, b` | `Signal dom T` | `if c t then a t else b t` | `Expr.op .mux [c,a,b]`（Bool は 0/1） | 組合せ | `mux_val`、`ir_mux_agrees` |
| `HAdd.hAdd.{0,0,0}`（`instHAddSignalBitVec dom w`） | `S,S,S,inst,a,b` | `Signal dom (BitVec w)` | `a t + b t`（mod 2^w） | `Expr.op .add [a,b]`（幅 w でマスク） | 組合せ | `addBV_val`、`ir_add_agrees` |
| `Signal.loop`（level なし） | `dom, T, Inhabited T, f` | `Signal dom T` | `loopGo f`（`Signal.loop` の純粋な定義。`implemented_by` は実行だけ） | レジスタ帰還（ループ変数 = レジスタ出力線） | t=0 は register の init、t+1 は cycle t を読む | `loop_val_zero`、`loop_register_map_succ`（`register i (map h s)` の形で `val (t+1) = h (val t)`） |
| `Signal.beq`（`instBEqOfDecidableEq (instDecidableEqBitVec w)`） | `α, dom, inst, a, b` | `Signal dom Bool` | `a t == b t` | `Expr.op .eq` | 組合せ | 規則 `sigBeqBV`（IR 側の一致は**この S1 では個別の補題を置いていない**: 端点の `machine_sound` に依る、§6） |
| `HAnd/HOr/Complement`（`instH…SignalBool`） | `S,S,S,inst,a,b` / `S,inst,a` | `Signal dom Bool` | `&&`, `||`, `!`（時刻ごと） | `.and/.or/.not` | 組合せ | 規則 `sigAndBool/sigOrBool/sigNotBool`（同上） |
| `let`/`have` | — | — | 束縛値を評価して環境に積む | なし | — | 規則 `letE` |
| `lam` | — | 依存関数型 | `fun a => …`（全称前提） | なし | — | 規則 `lam`（結果型が束縛変数に依存してよい: `(dom : DomainConfig) → …`） |
| `stIdle/stGrantA/stGrantB`（`abbrev … : BitVec 2`） | — | `BitVec 2` | `0#2/1#2/2#2` | `Expr.const` | 静的 | **具体的な境界** `bvAbbrevRow`（3 行、宣言の本体がそのリテラルであることを `FGCircuitPilotCheck` の meta 検査で照合。kernel では証明していない） |

per-cycle の合成（状態の受け渡し、`runModuleTG` の cycle 順、`Signal.loop` を register 帰還として読むこと全体）は、端点が使う既存の生成定理 `machine_trace_of_loop` / `machine_trace_of_data` に依る。パイロットはそれを再証明していない。

## 4. 元ソースから出力までの条件付きの接続（4 本）

対象: `Tests.SignalLoopTest` の `counterLoop` / `shift4Loop` / `counterEnableLoop`（D.D-4 e37da005 の 3 root）と、S0 の一覧が土台になかったので**フォールバックとして選んだ実 IP `Sparkle.IP.Arbiter.RoundRobin.arbiterSignal`**。理由: 出荷されている `IP/` の宣言で、Signal/BitVec の核（`loop/register/mux/===/&&&/|||/~~~`/`let`）だけで書かれ、定義域多相（既存の `shapeOf` の経路）、入力 2 本、状態ループ、出力 2 ビットを持ち、`#machine_endpoint` が通る。

各 root `X` について（`Tools/ShippingFGCircuitRoots.lean`。**公開する形は S1b の `X_root_at` / `X_ships_at`（`Tools/ShippingFGCircuitRootsAt.lean`、§6a）**。ここの `X_root` は env が run と独立の自由変数で、内部の部品として残す）:

1. `X_cd : CD [] <X の値の Expr> <型> X` — 値の `Expr` が `CD` で読め、読んだ値が**宣言 X そのもの**（`Signal.loop …` の unfold は kernel の delta で `rfl`）。3 root は手で組み、arbiter は `quote_value%`（宣言の値を `Expr` 項に引用）と `cdt` 戦術で導出。
2. `X_root`: 前提 `RootInEnv env X 型 値 d`・端点の run・`MachineDefines`・`MachineCloses` の下で
   `∃ mm, SourceDenotes(Mono) env X [] sh mm ∧ MachineTrace X X.machineData m dom (fun i bools bits => obs sh mm i bools bits)`。
   端点の `X.machineSource` は宣言自身の観測であり、`obs sh mm` と一致する（型が defeq で通る）。
3. `X_ships`: 同じ前提（`synthesizeCombinational`、`machine_ships_wired`）で、印字される module `b`（`dropZeroWidthModule`/`mergeChecked`、`checkedOptimize`、emit した Verilog の seq 検査）についての `MachineShips`。ソースは同じ観測。

`fgCircuit_of_H` は、生成表 `genGP` を通る一般の経路（`EntryWitness` からの `TopShips` と `DeclConnect CircCV`）が上と同じ結論の形になることを示す。**4 root の端点経路（`MachineTrace`）と `genGP` 経路（`Pkg`/`TopShips`）の統合は未実施**（§6）。

非自明性の確認（`FGCircuitPilotCheck`）: 引用した 4 つの値・型が実環境の宣言と `==`（meta）、`bvAbbrevRow` の 3 行が宣言のリテラルと `==`（meta）、`wrong_meaning_refused`（`shift4Loop` の観測は、常に 0 を返す偽の意味と同じ package で両立しない）、`params` が非空なら拒否、`Post := False` なら拒否、未知の定数は `CD` に入らない。

## 5. 実行結果

- build: `kjob lake build Tests.Gen5.FGCircuitPilotCheck`（exact-head と結果は Issue note）。
- S1b: `kjob lake build Tests.Gen5.FGCircuitPilotCheckAt`（`FGCIRCUIT SIGNATURES` / `SNAPSHOT` / `AXIOMS-AT` 行、§6a）。
- 出力行: `FGCIRCUIT META: 4 quoted roots equal the environment; 3 abbreviation rows equal their literals; machine_closes and machine_ships_wired exist for the 4 roots`、`FGCIRCUIT PRIMS: 7 rows, 13 proof references, all exist`、`FGCIRCUIT AXIOMS: … standard axioms only`。

## 6. 未解決の仮説（名前付き）と次に閉じる束

root 定理の前提（隠していない）:

| 名前 | 内容 | 状態 |
|---|---|---|
| `RootInEnv env X ty val d` | run の環境に `X` が型 `ty`・値 `val`（引用）で入っている | 実環境との一致は meta 検査のみ（kernel は環境を見ない）。`ENV/cache` の束（S2）に載る |
| run / `MachineDefines` / `MachineCloses` | 実行 `RunsTo (synthesizeCombinationalCore X [] false)`。`closes` は `X.machine_closes` がデータから出る（`closeEndpoint`）が、root 定理の前提としては置いたまま | S2（成功検査から導出） |
| 端点経路 ↔ `genGP` 経路 | root は `MachineTrace`/`MachineShips`、一般は `Pkg`/`TopShips`。`SrcPkg` を端点から作り `StepStmt` で `TopShips` に上げる接続は未実施 | S2 |
| `fgCircuit_of_H` の入力（未証明の H。FG 本体の根拠に数えない） | `FGLedgerPremisesStmtH`、`ReflectsAll Post lvl genData₀ L h_C_EN4 h_C_RK6 h_C_CV4`、内側の `h_A_P06`/`h_D_T4` | 既存の束のまま（FG 75 / T1 57 は減らしていない） |
| `ConstValueFunctional CircCV` | H の第 1 連言として H が出力する。`CD` の関数性は**未証明** | S2。`CD` は規則が構文で決まるので、証明は規則ごとの場合分けで済む見込みだが未測定 |
| `parameters = []` | S1 は記号パラメータなし | 必要 IP の一覧（S0）が出たら判断 |
| `bvAbbrevRow`（3 行） | 具体的な境界。値の一致は meta 検査 | 本体のリテラルを `unfold` する規則（環境つきの `CD`）に置き換えれば消せる |
| `sigBeqBV`/`sigAndBool`/`sigOrBool`/`sigNotBool`/`natLit` の IR 側の個別補題 | `machine_sound` の `Eq.refl` が実質の保証だが、パイロットの primitive 表の「IR の演算との一致」は register/mux/add/const/loop だけ個別に証明した | S2 で `eq/and/or/not` を追加 |

固定した信頼境界（新設）: なし。使うものは Lean kernel と標準 axiom、既存の IR 意味（`Sparkle.IR.Semantics`）、`Signal.loop` の純粋な定義（`@[implemented_by loopImpl]` は実行の高速化であり、論理の定義とは別。両者の一致は主張していない）。

発見した事実（reviewer への報告）:

1. 既存の `shapeOf`（`sigShape?`）は先頭に `(dom : DomainConfig)` の束縛がある宣言だけを受け付ける。`defaultDomain` に固定された 3 root は `shapeOf = none` なので、現行の `DeclConnect` は**対象にしない**。パイロットは `monoShapeOf`/`SourceDenotesMono`/`ObservationsEqualMono` を足した（位置は 0 から。`machineSource` の `bools 0`/`bits 0 8` と同じ規約）。必要 IP に定義域固定の宣言がある場合は S2 で `DeclConnect` 側の扱いを決める必要がある。
2. `CVEKV` の `prim`/`tcon` が `¬ IsDefn` を要求するため、`Signal.*` を停止する規則が書けない（§2）。「停止 7 key は Dyn に入る」という測定は、`PrimTableK` に defn の行を許す規則か、適用単位の規則（本パイロット）がなければ導出に使えない。

次に閉じる束（S2 への提案）: (1) 端点経路を `genGP` 経路へ（`SrcPkg` 化）、(2) `ENV/cache`（`RootInEnv` を run の環境から供給）、(3) `CD` の関数性と `eq/and/or/not` の IR 一致、(4) `closes` の供給、(5) S0 の必要 IP 全件に対する未対応構文の追跡。

## 7. 進捗の記録（戦略 §9、S1b で訂正）

(1) 必要 IP の成功数/総数: S0 の一覧がないので未計測。
(2) 元ソースから出力までの**条件付きの接続 4 本**（「閉じた経路」ではない）。各接続は次の前提を**まだ供給していない**:
- run の成功の存在（`hr : RunsTo (synthesizeCombinational…)`）、
- `RootInEnv (envAt cref w) X …`（run の開始環境に引用した `X` が入っていること）、
- `MachineDefines`（`hd`）、
- arbiter では `BoundaryRowsInEnv (envAt cref w)`（`hB`、§6a）。

`MachineCloses` は 4 root で供給済み（`X.machine_closes` はデータから出る全 context への定理で、`*_root_at` / `*_ships_at` が実際に適用する。型は `FGCircuitPilotCheckAt` が別記した期待型と照合する）。
(3) 位置づけ: `fgCircuit_of_H` は**未証明の H**（旧 CV の全称の問題を持つ `FGLedgerPremisesStmtH`）を `CV := CircCV` に特殊化しただけの橋で、FG 本体の証明にも非空虚性の根拠にも数えない。独立の参考部品である。
(4) `MachineShips` / `WiredConclusion` は `simpleBody`・`seqCheck`・`declWidth` の条件を結論の**内部**に持つ。印字した SV が元の意味を満たすことを無条件に保証したのではない（条件が成り立つ場合の含意）。
(5) 最終 root の未解決仮説と固定した信頼境界: §6。次に閉じる束: §6, §6a。
台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。

## 6a. S1b の訂正と境界（snapshot と任意の run 環境を区別する）

**公開する root（`Tools/ShippingFGCircuitRootsAt.lean`）**: `X_root_at` / `X_ships_at`（X = counterLoop / shift4Loop / counterEnableLoop / arbiterSignal）。`SourceDenotes(Mono)` の環境と `RootInEnv` の環境は、同じ run の開始環境 `envAt cref w` である。S1 の `X_root`（自由な `env`）は run と独立の環境を取れたので、別環境から引用を持ち込む取り違えを型が許していた。`X_root_at` はそれを許さない（`FGCircuitPilotCheckAt` が、`RootInEnv` または `SourceDenotes` を終了環境 `envAt cref w'` に置いた型、旧 `X_root`、を棄却する）。`RootInEnv (envAt cref w) …` の供給は、依然として**未解決の名前付き前提**（`hE`）である。

**独立の型 Check（`Tests/Gen5/FGCircuitPilotCheckAt.lean`）**: 4 root と 4 ships について期待型を別に書く（root 名・shape・machineData・開始 env・返す module をリテラルで）。実際の型と `MetaM` の `isDefEq`（machineData を評価しない構造照合）で比べ、一致しなければ失敗する。root 名、引用 type/value、shape、machineData、`RootInEnv` の env、`SourceDenotes` の env、boundary rows の env、返す module を 1 点ずつ取り違えた 15 mutant と、旧 `X_root` 4 本（計 19）を棄却する。`example … = … := rfl` や `#check` は署名の検査ではないので、これには数えない（旧 `FGCircuitPilotCheck` の該当行は参考）。

**arbiter の補助宣言（`bvAbbrevRow`）の境界**:
- `CD.bvAbbrev` は環境を読まず、`stIdle/stGrantA/stGrantB` に固定値 `0#2/1#2/2#2` を与える。`RootInEnv` は arbiter の root 自身についてだけで、3 つの補助宣言の意味との一致は含まない。
- **snapshot の事実**: この build の環境では、3 宣言は `bvAbbrevRow` のリテラルに等しい（`FGCIRCUIT SNAPSHOT` 行、`MetaM`）。これは固定した 1 つの環境についての検査であり、任意の run の環境についての主張ではない。
- **任意の run の環境についての主張**: 明示の条件 `BoundaryRowsInEnv (envAt cref w)`（`hB`）を `arbiterSignal_root_at` / `_ships_at` の前提に置いた。供給は未実施。kernel の証明は `hB` を使わない（`CD` は環境を見ない）ので、`hB` なしの旧 `arbiterSignal_root` は、環境の補助宣言が違えば `CD` の値と宣言の値が食い違い得る。
- **次の単位**（新しい TRUSTED にしない）: 環境付きの `CD`（`bvAbbrev` を `env.find?` と `unfold` で結ぶ規則: 宣言が `defnInfo` で値が `k#n` リテラルなら、その値を意味とする）に置き換えるか、`hB` を run から供給する（`ENV/cache` の束）。どちらを選んでも `bvAbbrevRow` の表は消える。

次の束（S1b の後）: 4 root の run の前提（`hr`, `hE`, `hd`）の供給、`CD` の関数性、`genGP` と同じ artifact への接続。U/P/I や全 51 行の作業には戻らない。
