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
- run の成功（`hr : RunsTo (synthesizeCombinational…)`）。【S1d で訂正】これは「供給できない」前提ではなく、「compile が成功したなら」の定理に自然に残る前件である。任意の入力について成功を証明する必要はない。必要 IP については、実際の compile の成功（S0 の baseline で 327/327。`docs/FG-CIRCUIT-BASELINE.md` は par/fgc-s0 5fe31f83 にあり、この worktree には無い）と、空虚でない適用例（§9.5）を別に示す。
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
- **次の単位**（新しい TRUSTED にしない）: 環境付きの `CD`（`bvAbbrev` を `env.find?` と `unfold` で結ぶ規則: 宣言が `defnInfo` で値が `k#n` リテラルなら、その値を意味とする）に置き換えるか、`hB` を run から供給する（`ENV/cache` の束）。【S1d で訂正】`hB` を run から供給するだけでは `bvAbbrevRow`（表）の定義は消えない（`CD.bvAbbrev` は表を引き続き読む）。消えるのは「表の値が環境の定義と食い違い得る」という隙間だけで、それは環境付きの unfold（`AbbrevDenotes`、S1c-4 の試作）を `CD` 本体の規則にしたときに限る。それまでは `bvAbbrevRow` は `hB` の下でだけ正しい具体的な境界である。

次の束（S1b の後）: 4 root の run の前提（`hr`, `hE`, `hd`）の供給、`CD` の関数性、`genGP` と同じ artifact への接続。U/P/I や全 51 行の作業には戻らない。

## 8. S1c（Issue `sparkle-fg-circuit-pilot` の次の束）: 閉じたもの・残る仮説・FG 行 ID

土台 `34ff2792`（par/fgc-s1）。追加ファイル（既存は書き換えていない）: `Tools/ShippingFGCircuitFunc.lean`、`Tools/ShippingFGCircuitArtifact.lean`、`Tools/ShippingFGCircuitSupply.lean`、`Tools/ShippingFGCircuitEnvCD.lean`、`Tests/Gen5/FGCircuitPilotCheck2.lean`（lakefile へは最初の commit で 1 回だけ登録）。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT2 AXIOMS`: 35 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。この束の成果は**条件付き**であり、「閉じた経路」とは書かない。
行 ID は `FGLedgerPremisesStmtG` の文面に現れる名前（A.P-02 / A.P-04 / D.D-1 / h_A_P06 / C.EN-4 / C.RK-6 / C.CV-4 / D.D-4 / D.D-3 / C.SM-1 / D.T-4 / A.P-05）で書く。台帳本体（8649968e §12.24）はこの worktree に無く読んでいないため、台帳の行番号との突き合わせは reviewer に残す。

### 8.1 閉じたもの（kernel で証明済み。無条件）

| 内容 | 定理 | 対応する FG の行 |
|---|---|---|
| 作業 1: `CD`/`TD` の関数性。同じ式・同じ valuation の 2 つの導出は同じ型・同じ値（`HEq`）。18 規則すべての組を検査（規則の衝突は先頭定数・構文の相違で棄却、同じ規則は部分式の帰納法） | `cd_fun`、`td_fun`、`cd_eq` | D.D-4 の `ConstValueFunctional` の一般形 |
| `CircCV` の関数性（D.D-4 の第 1 連言 `ConstValueFunctional CV` を `CV := CircCV` で満たす） | `circCV_functional` | D.D-4（H の第 1 連言）。**H 全体は未証明なので FG の行は減らさない** |
| 元ソースの意味は一意（同じ env・同じ宣言なら shape も意味も同じ） | `sourceDenotes_unique`、`sourceDenotesMono_unique` | — |
| 作業 2 の部品: package の `decl` は `genGP` から出る（仮定なし） | `genGP_decl`（`genP_decl`） | D.D-3（GP の固定） |
| 作業 2 の部品: 端点データ `X.machineData` と root の shape（引数数・出力ポート）が一致 | `counterLoop_shape` ほか 4 本（kernel の `decide`） | — |
| 作業 3 の部品: `MachineDefines` は「Core 状態が 1 つの環境 `E` を持ち続ける」と `E` についての環境レベルの命題 `MachineDefinesAt E X shape` に**還元できる** | `machineDefines_of_static`、`rootInEnv_of_static`、`boundaryRows_of_static` | h_A_P06（MachineDefines） |
| 作業 3 の部品: 成功した run は `X` を読む（`getConstInfo` の世界 `w1` の環境に `X` がある）。frame 仮定も引用の一致も不要 | `run_reads_root`、`run_reads_root_static` | A.P-04 |
| 作業 4: bvAbbrev の環境付き unfold の試作（`CD` 自体は変更なし）。`AbbrevDenotes env c n v` = 環境の定義の値を `CD` で読んだ値。`BoundaryRowsInEnv env` ⇒ 各行の `AbbrevDenotes`、環境の unfold による任意の意味は表の値に等しい（`cd_fun` による）、`BoundaryRowsInEnv` は env 定義の型・リテラル形と同値で、弱めていない | `abbrevDenotes_of_boundary`、`abbrev_unfold_eq_row`、`boundaryRows_iff_unfold` | ENV/cache（補助宣言） |

### 8.2 条件付きの接続（仮説を名前で残す）

- `X_artifact_at`（X = counterLoop / shift4Loop / counterEnableLoop / arbiterSignal）と、`genGP` を実際に使う `X_artifact_genGP`: 同じ env `envAt cref w`・同じ source 名・params `[]`・同じ `b`/`D` で、(i) `SourceDenotes(Mono)`、(ii) 同じ `mm` での package `p` との `ObservationsEqual(Mono)`、(iii) `HasConcretePackage p n X b raw D`（`TopShips`）、(iv) `WiredConclusion`（run が返す印字 module `b`）を束ねる（`RootArtifact(Mono)`）。`p` は `genGP lvl hs genData₀ (envAt cref w) X = some p` で与えられ、`p.decl = X` は仮定なしで出る。
- `X_root_static`: `hE`/`hd`/`hB` を、1 つの環境 `E` についての環境レベルの命題と `StaticEnv cref E` に置き換えたもの（作業 3）。
- 結論は FG の形 `FGCircuitConclusionMono`（`fgCircuitConclusionMono_of_artifact`）に収まる。

### 8.3 残る仮説（名前付き。Check2 の `FGCIRCUIT2 HYPS` が型から読み出す）

| 仮説 | 内容 | 未供給の理由 | FG の行 |
|---|---|---|---|
| `hr` | run の成功 `RunsTo (synthesizeCombinational…) … w (b, D) w'` | 【S1d で訂正】供給する対象ではなく、「compile が成功したなら」の定理の前件として残す（コンパイラが宣言に対して走って返ることを全入力で証明する必要はない）。`MachineCloses` は「機械合成が走ったなら `none` を返さない」であり、成功そのものの存在は主張しない | A.P-04（`EntryWitness` の run）、A.P-02（Start） |
| `hE`（`RootInEnv (envAt cref w) …`） | run の開始環境に引用した `X` が入っている | 環境は実行時の値。kernel は `counterLoop` という Lean 定数の値を知るが、コンパイラが読む `Environment` 値がそれであることは言えない。`run_reads_root` は「何らかの `ci` を読む」までしか出さない（引用との一致は meta 照合 `SNAPSHOT2`） | C.EN-4（CellPrem）、ENV/cache |
| `StaticEnv cref E`（`_static` 版） | Core 状態が全 world で同じ環境 `E` | run の途中で Core 状態の `env` が変わらないという frame 性質。`Tools/ShippingEntryReadsLinked.lean` の `EnvSnapshot`（開いたまま）の全 world 版 | C.EN-4 |
| `MachineDefinesAt E X shape`（`hd`） | `E` の `X` について `certifiedShape?`/`mixedCertifiedShape?` が `none`、`machineShape?` が `some shape` | `instancePredicate E`/`userInliner E`/`structEnv E` は環境全体を読む。`RootInEnv` は `X` 自身の型と値しか言わない | h_A_P06、C.RK-6、C.CV-4 |
| `hB`（arbiter の `BoundaryRowsInEnv`） | 補助 abbrev 3 つが `bvAbbrevRow` のリテラル | 作業 4 で環境の unfold と同値であることは示したが、環境の定義が何かは実行時の環境の事実 | ENV/cache |
| `hl`（`EndpointLink`） | `p.d = X.machineData`、`p.kD`、`p.src` が端点の観測 | `p.d` は `dataOfAt …`（`GenPDEdgesStmt`）、`X.machineData` は `readMachine`。`Tools/ShippingGen5DataOf.lean` が「木に無い」と書く `dataOfAt` ↔ `readMachine` の橋。`p.src` は `genSem` の観測 | DG-DATAOF / DG-COVER（`C.SM-1` の `hs` と別の行） |
| `hTop` | 印字 `b` についての `TopShips p n X b raw D` | `WiredConclusion`/`MachineShips` から `TopShips` に上げる定理は木に無い（`StepStmt` の領分）。`WiredConclusion` は `simpleBody`・`seqCheck`・`declWidth` の条件を内部に持つ | D.T-4 / `StepStmt` |
| `hP` | `genGP … X = some p` | 生成表が `X` で `some` を返すこと（被覆）。**この束では供給していない** | D.D-3 / O2（coverage） |
| `fgCircuit_of_H` の入力 | 未証明の H | 変更なし。FG 本体の根拠に数えない | H 全体 |

### 8.4 作業 2 の結論と未実施

root の文（`X_ships_at`）と生成表（`genGP`）は、**同じ環境・同じソース名・同じ `b`/`D`・同じ `mm`** で 1 つの定理に束ねた。ただし束ねたのは「`p` が端点であること（`hl`）と `TopShips`（`hTop`）を仮定したとき」であり、`genGP` の `p` が実際に端点データを持つこと、印字 `b` が `TopShips` を満たすことは**示していない**（8.3）。したがって「閉じた経路」ではなく、条件付きの接続である。

### 8.5 台帳

台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。`circCV_functional` は H の 1 連言（D.D-4）を `CV := CircCV` で満たすが、H の他の連言と `CV` binder の置換が受理されていないので数を減らさない。

### 8.6 次の束

(1) `StaticEnv` と `MachineDefinesAt` の供給（`coreHead` が Core 状態の `env` を変えない frame 補題と、`MachineDefinesAt` を具体の `Environment` 値に対して評価する meta 検査）。(2) `dataOfAt` ↔ `readMachine` の橋（`hl` の `p.d`）。(3) `WiredConclusion` → `TopShips`（`StepStmt` の単一モジュール版）。(4) `hr`: run の存在。

## 9. S1d（Issue `sparkle-fg-circuit-pilot` の次の束）: 供給した前提・残る前提・訂正

土台 `87c713c6`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile へは最初の commit で 1 回だけ登録）: `Tools/ShippingFGCircuitSupply2.lean`、`Tools/ShippingFGCircuitCover.lean`、`Tools/ShippingFGCircuitBridge.lean`、`Tools/ShippingFGCircuitApply.lean`、`Tests/Gen5/FGCircuitPilotCheck3.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT3 AXIOMS`: 29 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。この束の成果も**条件付き**であり、FG の行は減らさない。
訂正（§6a 末尾の「どちらでも表は消える」、§7 と §8.3 の `hr` の書き方）は該当箇所に「S1d で訂正」と書いた。

### 9.1 作業 1: `StaticEnv` / `MachineDefinesAt` / `hE` の供給

| 内容 | 定理 | 結果 |
|---|---|---|
| **`StaticEnv` は C.EN-4 の下で偽**。`StaticEnv cref E` は全 world で `envAt cref w = E` と言うが、`CellPrem`（C.EN-4）の一部 `SetGet cref` の下で、Core 状態を別の環境（`setMainModule` で作った 2 つ）に `set` した world が作れるので `¬ StaticEnv cref E` | `not_staticEnv` | S1c の `X_root_static`（§8.2）は前提が C.EN-4 と両立しない含意になる。**供給の経路として使わない**。§8.3 の `StaticEnv` の行は「供給できない」ではなく「述べ方が不適」に訂正する |
| `hd`（`MachineDefines mctx mref cctx cref X shape`）を **h_A_P06**（`FGLedgerPremisesStmtG` の内側の仮説）の root での適用（`TgtRun.top`）から供給。`Start`（A.P-02）から admissible context、`genGP` の package から `p.d.shape = X.machineData.shape` | `machineDefines_of_hA6`、`machineDefines_of_witness` | 供給（h_A_P06 は名前付き前提のまま） |
| `hc`（`MachineCloses`） | `X.machine_closes`（S1c から。`machineClosesAtA_of_closes` で `Bridge` の run 証拠にも使う） | 供給 |
| `hE`（`RootInEnv (envAt cref w) …`）: run が実際に読んだ `getConstInfo X` の world `w1` の環境に `X` がある（存在は run から出る）。開始環境への移送は **run 局所**の `EnvSnapshot cref w1 w`（既存の open な文）。中身（その定義が引用と一致）は `QuoteFact`。`∀ w` の `StaticEnv` は使わない | `run_reads_const`、`rootInEnv_of_quote`、`hE_of_run` | 存在は供給。残る: `QuoteFact`（環境の `X` の中身）と `EnvSnapshot`（C.EN-4 / ENV cache） |
| `MachineDefinesAt` の実環境での値 | `FGCIRCUIT3 SNAPSHOT3` | この build の環境で 4 root について `certifiedShape? = none`・`mixedCertifiedShape? = none`・`machineShape? = some` を MetaM で評価（一つの環境の値であり、任意の run の環境についての主張ではない） |

注意（reviewer へ）: `MachineDefines` と h_A_P06 は run と無関係な world `w1 w5 w7` について `∀` で書かれている（`RunsTo getEnv … w5 envR w6` は任意の world で成り立つ）。`StaticEnv` と同じ形の強さがあり、`SetGet cref` の下で充足可能かどうかは**この束では調べていない**。`hd` を供給できたのは、この強い形の h_A_P06 を前提として受け取ったからである。

### 9.2 作業 2: `hl`（`dataOfAt` と `readMachine` の橋）

`EndpointLink` の 3 つの連言のうち `data`（`p.d = X.machineData`）と `kD_eq`（`p.kD = kDOf X.machineData`）を示した（`genGP_root`、`genGP_root_canon`）。`genGP` が返す package の `d` は `genP_d_edges` により table の行 `g` の `g.d` で、`g.hdata : dataOfAt lvl E senv g.d.shape = some g.d`、`g.hshape : machineShape? … = some g.d.shape`。したがって次の**名前付き前提**があれば `p.d = X.machineData`:

`RootReader lvl env X d := ∃ E, entry₀ env X = some E ∧ machineShape? false [] E (structEnv env) = some d.shape ∧ dataOfAt lvl E (structEnv env) d.shape = some d`（`d := X.machineData`）。

これは `dataOfAt` と `readMachine` の出力の一致をリテラル `X.machineData` に対して述べたもの（FG 行: DG-DATAOF / DG-COVER / DG-ENV。C.SM-1 の `hs` とは別）。**kernel では未供給**（【S1f で訂正】「示せない」とは断定しない）: `dataOfAt` が `partial` の `packTupleInputs` / `rootFloat` を呼び、kernel は評価できない。`FGCIRCUIT3 SNAPSHOT3` は実環境で `dataOfAt`（fuel `fun _ => 1000000`）を評価し、4 root で nIn・#state・#outs・#lets・#insts・#binders・ok・GenWF がリテラルと一致することを確かめた。`MachineData` に `Repr`/`DecidableEq` が無いので**完全な一致ではなく不変量の比較**である。

`src`（`p.src = X の観測`）は示していない。`p.src` は `genSemGenE` の `stateLoop` による観測、右辺は宣言自身の `Signal.loop` の観測で、両者の一致は D.D-3 のこの root での意味の内容そのものである。必要なもの: (a) `stateLoop` と `Signal.loop` の時刻 t についての帰納（`machine_source` と `machine_result` が右辺側を与える。左辺の `refBodyE` は insts = [] で `extB/extS` が恒等になる）、または (b) 同じ run の module に対する 2 つの trace（`Pkg.trace` と `X.machine_sound`）から、出力値の一意性で `p.src = obs` を出す（`SourceInputs` を実現する `ins` の構成が要る）。どちらも未実施で、`hsrc` として残す。

### 9.3 作業 3: `hTop`（`WiredConclusion` から `TopShips`）

`WiredConclusion` からは作らない（`MachineShips` は最適化後 module と Verilog の `wof` についての文で、`TopShips` は階層実行 `runModuleTG` の文）。代わりに、4 root が**レジスタ付きの leaf**（`insts = []`、`slots ≠ []`）であることを使い、既存の `leaf_topShips_of_LB`（`Tools/ShippingGen2Leaf.lean`）と trace の生成子 `Pkg.trace L.O L.T hA p ran` を使った。`ran` は `machineRunJQC_of_closesA`（core run、`MachineDefines`、`MachineClosesAtA`）から作る。

- `leaf_topShips_of_run`: `Start`・core run・`hd`・`hc`・`PostT1 b raw`・data の判定可能な事実 `LeafFacts`（`decide`。4 root で成功）から `TopShips p n X b raw D₀`（**D₀ = core run の design**）。
- `hTop_of_leaf`: `Post := PostRun`（core run に結んだ後処理関係）の下で `∀ raw, PostRun … → ∃ n, HasConcretePackage p n X b raw D'`。ただし **core design D₀ から印字 design D' への移送 `DesignTransport`** を名前付き前提とする。移送の部品は `Tools/ShippingGen5DCEntryT.lean`（`childMap_transport`、`runModuleTG_transport`）にあるが、同ファイルは NOT BUILT・条件付き（`NoRawBelow`、lookup の一致）で、`TopShips` 自体の移送は木に無い。
- `A.P-05` の `Post` は抽象の carrier なので、そこから `raw` が core run の出力だと言えない。`PostRun` はその関係を run に結んだ値である（`∃ raw, Post` は `hr` と `synthesizeCombinational_postEntry` から供給）。

### 9.4 作業 4: `hP`（`genGP` の被覆）

`genGP_root`: leaf の root で、table `genData₀ env` が `entry₀ env X` に行 `g` を持つなら `genGP … X = some p`（`insts = []` なので `Acc (CallRel K) X` は空虚に成り立ち、`ordCallees` は空で、`ReachCover` は一つの名前に落ちる）。`p.decl = X`、`p.d = g.d`、`p.kD = kDOf g.d` も同時に出る。`canonGD`（`GenData` が存在すれば選ぶ table）では、行は `RootReader` と `GenWF`（`decide`）から作れる（`genGP_root_canon`）。`genGP` を具体的に計算する経路は無い（環境が閉じた項でない）ので、被覆は具体計算ではなく `RootReader` に還元した。任意の `genData₀` については行の存在が前提になる（`genGP_root` の `hg`）。

### 9.5 作業 5: 適用例

`counterLoop_final`、`shift4Loop_final`、`counterEnableLoop_final`、`arbiterSignal_final`（`Tools/ShippingFGCircuitApply.lean`）。各定理の仮説は次の**だけ**（`FGCIRCUIT3 HYPS` が型から読み出し、期待の一覧と一致することを検査する。`hd`/`hc`/`hP`/`hl`/`hTop`/`hpost` が仮説に戻ったら失敗する）:

| 仮説 | 内容 | FG の行 |
|---|---|---|
| `hw : EntryWitness …`、`hr` | compile が成功した（antecedent） | A.P-02 Start、A.P-04 run |
| `hA6` | h_A_P06 | h_A_P06 |
| `hRead : RootReader` | `dataOfAt`/`machineShape?` が実環境の root でリテラルのデータを返す | DG-DATAOF / DG-COVER / DG-ENV |
| `hE`（arbiter は `hB` も） | 環境の `X` の中身（`QuoteFact` + `EnvSnapshot`） | C.EN-4 / ENV cache |
| `hsrc` | `p.src` が宣言の観測 | D.D-3（DG-SEM） |
| `htr : DesignTransport` | core design → 印字 design | D.T-4 / `StepStmt` |

定理の内部で供給したもの: `hd`（h_A_P06 から）、`hc`、`hP`、`p.decl`/`p.d`/`p.kD`、leaf の判定可能な事実、core design での `TopShips`、`∃ raw, PostRun`、shape の一致、`SourceDenotes`。結論は `∃ raw, PostRun …` と、`P := genGP … (canonGD lvl) (envAt cref w)` の `RootArtifact(Mono)`。

**未供給の前提（明記）**（【S1f で訂正】「満たせない／作れない」ではなく、現在の定式化では未供給）: kernel の中で `hw`/`hr`（走った run）、環境に関する `hE`/`hB`/`hRead`、`hsrc`、`htr` を実際の値で満たした項は現状ない（run も `Environment` も、この束では閉じた項として構成していない）。したがって「全前提を実際の値で満たした適用例」は kernel の中には**未構成**である。代わりに: (a) leaf の事実・`GenWF`・`kD` は 4 root で実際のリテラルに対して `decide` した（`X_leafFacts`、`X_wf`、`X_kD`）、(b) 環境に関する `hE`/`hB`/`hRead` と `MachineDefinesAt` の 3 つの事実は、この build の実環境で MetaM が評価した（`SNAPSHOT2`、`SNAPSHOT3`）、(c) compile の成功そのものは S0 の baseline（327/327）が示す。`hsrc`/`htr` はどこでも評価されていない。この束で条件付き定理が空虚でないことの根拠はここまでで、それ以上ではない。

### 9.6 Check3 の出力

`kjob lake build Tests.Gen5.FGCircuitPilotCheck3`（exact-head と結果は Issue note）。出力行: `FGCIRCUIT3 SIGNATURES`（`not_staticEnv`・`machineDefines_of_hA6`・`genGP_root_canon` の期待型と 6 mutant）、`FGCIRCUIT3 HYPS`（4 root の仮説一覧）、`FGCIRCUIT3 AXIOMS`（29 名）、`FGCIRCUIT3 SNAPSHOT3`。`X_final` の期待型の独立記述と mutant は作っていない（仮説一覧と「自分の root だけを含む」検査で代えた）。

### 9.7 残る仮説（名前付き。台帳は FG 75 / T1 57 のまま）

`hr`/`hw`（A.P-04、A.P-02。前件）、`hA6`（h_A_P06。`∀`-world の形に注意、§9.1）、`RootReader`（DG-DATAOF / DG-COVER / DG-ENV）、`QuoteFact` + `EnvSnapshot`（C.EN-4 / ENV cache。arbiter は `hB`）、`hsrc`（D.D-3）、`DesignTransport`（D.T-4）。任意の `genData₀` では table の行の存在。`fgCircuit_of_H` の入力（未証明の H）は変更なし。
次の束: (1) `hsrc`（stateLoop と Signal.loop の帰納、または 2 trace の一意性）、(2) `DesignTransport`（`DCEntryT` の移送を `TopShips` まで持ち上げる）、(3) `MachineDefines`/h_A_P06 の `∀`-world の形が `SetGet` の下で充足可能かの確認、(4) `RootReader` を kernel で扱える形（`partial` helper の外出し）にするか、MetaM の検査器として固定するかの判断。

## 10. S1e（Issue `sparkle-fg-circuit-pilot` の次の束）: counterLoop 1 root の実接続

土台 `306716c3`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回だけ）: `Tools/ShippingFGCircuitSrc.lean`、`Tools/ShippingFGCircuitTransport.lean`、`Tools/ShippingFGCircuitFinal.lean`、`Tests/Gen5/FGCircuitPilotCheck4.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT4 AXIOMS`: 12 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**（残る前提あり）。方針どおり 4 root を並行せず counterLoop だけを閉じた（他 3 root は `X_final` のまま、`hsrc`/`htr` が前提に残る）。

### 10.1 作業 1: `hsrc`（D.D-3: stateLoop と Signal.loop）— 供給した

`counterLoop_hsrc`（`Tools/ShippingFGCircuitSrc.lean`）: `RootReader lvl env counterLoop counterLoop.machineData` から、`genGP … (canonGD lvl) env counterLoop = some p` なる `p` が存在し、`p.src i bools bits = monoObs shCounter counterLoop bools bits`。
経路: (1) `genGP_root_src` / `genGP_root_canon_src`: package の `src` は表の行 `g` について `(genSemI (genS K) X (g.toIn hs)).src`（`genP_some_inv`、`src_toSem`、`GenData.genSem` は定義上 `genSemI`）。`g.d = X.machineData`（`canon_row`）、`inits = initsOf g.d`（`toIn` が定義上そう置く）。
(2) `counterLoop_src_eq`: そのような `GenIn` について `(genSemGen Q X gi).src = counterLoop.machineSource`。`insts = []` なので `extBOf/extOf` は恒等（`ExtStage … 0`）。生成側の状態ループ `stateLoop inits (refBodyE …)` と宣言側の `Signal.loop counterLoop.machineBody` の状態が、cycle t ごとに `machineSigma`（`x ↦ (x, ())`）で対応することを t の帰納で示した: 初期値は `initsOf machineData = machineInits`（`rfl`）と `R.val 0 = 0#8`、1 step は `loop_state`（生成側）・`genSemGenE_writes`・`counterLoop.machine_writes`（宣言側。`evalTerms (typedVal …)` が同じ項 `machineData.nexts` を評価する）。出力は `genSemGenE_result` と `counterLoop.machine_result` / `machine_source` から各 cycle で一致し、`list_ext_of_map_eval` でリストが等しい。
意味: 両辺は**同じ項**（`machineData.nexts/outs`）を評価するので、この一致は「reader が読んだデータが宣言のコピー（`RootReader`）であること」を使っており、データが宣言の意味であること自体は `X.machine_sound` / `machine_writes`（endpoint の kernel `Eq.refl`）に依る。示せていないもの: `RootReader`（`dataOfAt` の実環境での値、MetaM 検査のみ）。

### 10.2 作業 2: `DesignTransport`（D.T-4）— レジスタ leaf について供給した

`designTransport_of_leaf`（`Tools/ShippingFGCircuitTransport.lean`）: core run の `(raw, D₀)` と印字 design `D'` について `TopShips p n X b raw D₀ → TopShips p n X b raw D'`。`D'` は任意の design でよい（`PostEntry` の `topMap …` である必要もない）。
理由: `TopShips` は design を `childMap D.modules`（instance の oracle）と `ResetNk n raw D kids` を通してのみ読む。レジスタ leaf の `raw.body`・`b.body`・`(checkedOptimize b).body` は `seqStmtOk`（assign/register/memory）で **instance を持たない**（`MachineWired` の `hclean` と `leaf_b_facts` から読む。`leaf_instFree_of_run`）。よって `runModuleTG_instFree` で run は oracle に依らず、`ResetNk` は空虚、`bodyInstOuts _ b.body = []`（`bodyInstOuts_instFree`）。`topShips_design_irrel`。
`Tools/ShippingGen5DCEntryT.lean`（`childMap_transport`、`runModuleTG_transport`）は **instance を持つ module 用**で、この経路では使っていない。同ファイルは単独で build できる（`kjob lake build Tools.ShippingGen5DCEntryT` exit 0、354 jobs）。非 leaf の root への持ち上げでは `NoRawBelow` と lookup 一致が要る。
追加の前提は無い（`hr` の core run、`hd`、`hc`、`LeafFacts`、`PostT1` は S1d で既に供給済みのもの）。

### 10.3 作業 3: counterLoop の最終定理

`counterLoop_final2`（`Tools/ShippingFGCircuitFinal.lean`）。仮説は **`hw`、`hr`、`hA6`、`hRead`（RootReader）、`hE`** だけ。`hsrc` と `htr` は仮説から消えた（`counterLoop_final` から比較）。`hTop_of_leaf2` は transport の前提なしで `∀ raw, PostRun … → ∃ n, HasConcretePackage p n X b raw D'`。
結論は S1d と同じ: `(∃ raw, PostRun …) ∧ ∃ mm p, RootArtifactMono (envAt cref w) (genGP … (canonGD lvl) (envAt cref w)) (PostRun …) counterLoop shCounter mm b D' p`。

残る前提（名前付き。台帳は FG 75 / T1 57 のまま）:

| 仮説 | 内容 | 状況 |
|---|---|---|
| `hw` / `hr` | compile が成功した（`EntryWitness`、`RunsTo (synthesizeCombinational counterLoop)`） | 前件。S0 baseline で成功は確認済みだが kernel の中では供給しない |
| `hA6` | h_A_P06（`∀`-world の形） | reviewer が `SetGet` 下の充足可能性を確認中。この束では扱わない |
| `hRead : RootReader` | `dataOfAt`/`machineShape?` が実環境で `counterLoop.machineData` を返す | MetaM の実環境検査（`SNAPSHOT3`）。kernel では未供給（`partial` helper を呼ぶため、現在の定式化では評価していない） |
| `hE : RootInEnv` | 環境の `counterLoop` が引用した値 | `QuoteFact` + `EnvSnapshot`（C.EN-4 / ENV cache） |

`hsrc` と `DesignTransport` は counterLoop の最終定理から消えたが、`hsrc` は `RootReader` を使う。他の 3 root（shift4Loop、counterEnableLoop、arbiterSignal）の `X_final` はそのまま（`hsrc`/`htr` を仮説に持つ）。`hsrc` の証明は `counterLoop` 固有の項（`machineBody`、`machineSigma`、`machine_writes`）で書いたため、他 root には root ごとの同形の証明が要る（`DesignTransport` は 4 root とも同じ理由で供給できる）。

### 10.4 Check4 の出力

`kjob lake build Tests.Gen5.FGCircuitPilotCheck4`（884 jobs、exit 0）。出力行: `FGCIRCUIT4 SIGNATURES`（`counterLoop_hsrc`、`designTransport_of_leaf`、`counterLoop_final2` の期待型 3 本が独立記述と一致、8 mutant 棄却）、`FGCIRCUIT4 HYPS`（`counterLoop_final2` の仮説は `L lvl hw hr hA6 hRead hE`。`hsrc`/`htr`/`hd`/`hc`/`hP`/`hl`/`hTop` は仮説に無い）、`FGCIRCUIT4 AXIOMS`（12 名、標準 axiom のみ）、`FGCIRCUIT4 SNAPSHOT4`（`counterLoop.val 0 = 0`、`counterLoop.val 3 = 3` を kernel が証明: 観測が自明でない）。
限定: 適用例（全前提を実際の値で満たす例）は kernel の中には未構成（§9.5 と同じ。run も `Environment` もこの束では閉じた項にしていない。【S1f で訂正】「作れない」とは断定しない）。

### 10.5 次の束

(1) 他 3 root の `hsrc`（shift4Loop はレジスタ 4 段、counterEnableLoop は mux、arbiterSignal は domain 多相で、counterLoop と同形の帰納が使えるかを root ごとに確認）。(2) `hA6`（reviewer 判断待ち）。(3) `RootReader` / `hE` を MetaM の検査器として固定するか、kernel で扱える形にするかの判断。

## 11. S1f（Issue `sparkle-fg-circuit-pilot` の次の束）: counterLoop の run 局所化

土台 `07e5b53c`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回だけ）: `Tools/ShippingFGCircuitRunLocal.lean`、`Tools/ShippingFGCircuitRunLocal2.lean`、`Tools/ShippingFGCircuitFinal3.lean`、`Tests/Gen5/FGCircuitPilotCheck5.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT5 AXIOMS`: 18 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。方針どおり 1 root（counterLoop）だけを扱った。§9・§10 の「作れない／示せない」の断定は「未供給」に訂正した（§8.3 の表の見出し、§9.2、§9.5、§10.3、§10.4 の該当文）。

### 11.1 `hw` を `Start` + `hr` に絞った（`counterLoop_final3`）

`hw : EntryWitness ReflectsAll L …` は `Start`・run・`ReflectsAll L declName parameters` の連言だった。S1e までの証明が使っていたのは `hw.1`（`Start`）と `hr` だけで、`ReflectsAll` は供給も使用もされていなかった。`counterLoop_final3`（`Tools/ShippingFGCircuitFinal3.lean`）の仮説は `L lvl hstart hr hdRun hRead hE`（`hw`・`ReflectsAll`・`hA6` なし）。`Laws L`（A.P-02 の runtime laws。`Start` の `AdmCtx`/`JQC` の前提でもある）は明示引数のまま**残る義務**で、型に出ている。

### 11.2 `MachineDefines` → `MachineDefinesRun`（run に局所化した境界）

`MachineDefines`（および h_A_P06 の `hA6`）は、run と接続されていない world `w1 w5 w7` の `getConstInfo`/`getEnv` について `∀` で書かれている。後継 `MachineDefinesRun mctx mref cctx cref X shape w M D w'`（`Tools/ShippingFGCircuitRunLocal.lean`）は同じ 3 つの事実（`certifiedShape?` = none、`mixedCertifiedShape?` = none、`machineShape? = some shape`）を、**core run `synthesizeCombinationalCore X … w (M, D) w'` が実際に読んだ値**についてだけ要求する:

- `ci` と `envR` は、run の本体 `synthesizeFromConst … ci envR` が呼ばれた値（`synthesizeCombinationalCore_reads` の分解。その run `w3 → w4` が `(M, D)` を返すことが前提）。
- `envR'` は、`synthesizeFromConst` が最初に行う `getEnv` の結果で、**その本体の開始 world `w3` に結んである**（`synthesizeFromConst_machine_invR` / `synthesizeFromConst_machineR`: 既存の `…_invA` / `…_machine` は `w5` が任意の world だった。証明を写して文だけ強めた）。
- 読み取り world `w1`（getConstInfo）と `w5`（最初の getEnv）は、返した値が同じになる任意の world で、run の実際の world に固定してはいない（`RunsTo` は決定的だが、値だけを固定している）。この点で「run の分解に対する ∀」であり、全 world の ∀ より狭いが、1 つの world への一点指定ではない。

`machineDefinesRun_of_defines`: `MachineDefines` ⇒ `MachineDefinesRun`（逆は主張しない）。SetGet だけから `MachineDefines` が偽だとは断定しない（S1d の判断どおり）。局所化後の述語は充足可能性を主張せず、供給もしていない。

**消費者まで接続した**:
- `machine_run_of_coreR` / `machineRunJQC_of_closesR`（package の trace、leaf の `TopShips`、`DesignTransport` が使う `MachineRunJQC`）。
- `synthesizeCombinationalCore_machine_soundR`。
- endpoint 側: 生成された `counterLoop.machine_ships_wired hr hd hc` は `hd : MachineDefines` を取る。`Tools/ShippingFGCircuitRunLocal2.lean` は既存の `machine_trace_lets_of_streamB` / `machine_trace_lets_of_stream` / `machine_traceL_of_stream` / `machine_traceL_of_loop` / `machine_ships_wired` の**証明の写し**で、境界の前提だけを `MachineDefinesRun`（`machine_ships_wiredR` では `∀ raw D w1, MachineDefinesRun … w raw D w1`）に替えた（`…R` 名）。`counterLoop` の endpoint は `machine_ships_wired d (machine_traceL_of_loop …)` の形（生成された項を `#print` で確認）なので、同じ引数で `…R` に差し替えられる。
- `hTop_of_leaf3` / `leaf_topShips_of_runR` / `leaf_instFree_of_runR`（`DesignTransport` を含む）、`counterLoop_artifact_atR`、`counterLoop_final3`。

`counterLoop_final3` の `hdRun : ∀ raw D₀ w1, MachineDefinesRun … ``counterLoop counterLoop.machineData.shape w raw D₀ w1` が、旧 `hA6` の代わりに残る**未供給の義務**（FG の h_A_P06 の run 局所形）。h_A_P06 から `MachineDefines` が出れば `machineDefinesRun_of_defines` で `hdRun` が出る、という一方向の関係だけを主張する。

### 11.3 `hRead` / `hE` の局所化（試行: `counterLoop_final3L`）

run が実際に到達する地点は 3 つ: `getConstInfo X`（world `w1`）、最初の `getEnv`（`w5`、entry constant の計算元）、`synthesizeFromConst` 内の 2 度目の `getEnv`（`w3`、`machineShape?` の読み取り元）。`OnRunReads`（`MachineDefinesRun` と同じ分解）の上に 3 つの名前付き義務を作った:

- `RunSnap`: 3 つの読み取り world の環境が開始 world の環境と等しい（run 局所の `EnvSnapshot`。C.EN-4 / ENV cache）。
- `RunQuote`: run が読んだ `ci` は引用した定義（`QuoteFact` を run の `ci` に限ったもの）。
- `RunReader`: 読み取り関数 `dataOfAt` を、run の `ci`/`envR` の entry constant と開始環境の `structEnv` に適用した結果が `X.machineData`（DG-DATAOF / DG-COVER / DG-ENV）。

`rootEnv_of_run`（`hdRun` の 3 つ目の事実と合わせて）から `RootInEnv (envAt cref w)` と `RootReader lvl (envAt cref w)` が出る（`RootReader` の `machineShape?` の連言は仮定ではなく `MachineDefinesRun` の 3 つ目の事実になる）。`counterLoop_final3L` の仮説は `L lvl hstart hr hdRun hsnap hquote hreader`。結果: **局所化はできた**が、`RunSnap` の 3 条件（C.EN-4 の下で `∀ w` ではなく run の 3 地点だけ）、`RunQuote`、`RunReader` は未供給のままで、数は `hE`（QuoteFact + EnvSnapshot）+ `hRead` から減っていない（`MachineDefinesRun` の 3 事実のうち `machineShape?` を `RunSnap` で移して `RootReader` から落とした分だけ義務の置き場所が変わった）。`hRead`/`hE` 形の `counterLoop_final3` も残してある。`RunSnap` が `SetGet` の下で充足可能かは調べていない。

### 11.4 Check5 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck5`、887 jobs、exit 0）

- `FGCIRCUIT5 SIGNATURES`: `MachineDefinesRun`、`counterLoop_final3`、`counterLoop_final3L`、`hTop_of_leaf3`、`rootEnv_of_run` の期待型を**型全体**（仮説・結論・環境・design・binder の種類）で独立に書いて `isDefEq` で照合（`MachineDefinesRun` は独立に書いた文と照合）。22 mutant 棄却: 環境（P/結論・`hRead`・`hE`・`RunSnap`）、design/Post の root、`hdRun` の shape、`hRead` の data、package の table（`lvl`）、`Start`/`hr` の欠落、旧 `EntryWitness` の追加、結論の弱め、`MachineDefinesRun` の world の結び（w3→w5）・shape を読む環境・`entryConst` の bool・`getConstInfo` の名前。
- `FGCIRCUIT5 HYPS` / `REMAINING`: 2 つの最終定理の仮説名と型。`hw`・`ReflectsAll`・`hA6`・全 world の `MachineDefines`・`hsrc`・`DesignTransport` は仮説に無いことを検査。
- `FGCIRCUIT5 AXIOMS`: 18 名、標準 axiom のみ。
- `FGCIRCUIT5 SNAPSHOT5`: この build の環境で `dataOfAt`（fuel 1000000）の結果を、endpoint の `counterLoop.machineData` の**全構造**（endpoint コマンドが組み立てる Expr を観測値からフィールドごとに再構成: shape の binders/body/layout/runs/insts/loops/instFields/instOrigins、nIn、dom、位置、sort、lets、outs、nexts を項として）と比較して一致。負対照: shift4Loop の data と、10 個の 1 フィールド摂動を棄却。観測値（nIn=0、状態 1 本 8 bit、binder `loop0_r0`、layout、outs=`bitsInput 8 0`、nexts=`add (bitsInput 8 0) (bitsLit 8 1)`、body）も表示。`certifiedShape?` = `mixedCertifiedShape?` = none、`machineShape?` が reader の shape と一致。これは**ひとつの環境の値**で、任意の run についての `RootReader`/`RunReader`/`MachineDefinesRun` の kernel の文ではなく、前提が同時に充足可能であることの証明でもない。

### 11.5 閉じたもの、残る仮説、FG の行 ID との対応

閉じた（kernel 証明として、仮説つきで）:

| 内容 | 定理 | FG の行 |
|---|---|---|
| `hw` から `ReflectsAll` を外し `Start`+`hr` へ | `counterLoop_final3` | A.P-02 / A.P-04 |
| `MachineDefines` の局所版と、それを使う endpoint 連鎖 | `MachineDefinesRun`、`machine_ships_wiredR` ほか | A.P-06（h_A_P06） |
| leaf の `TopShips`・`DesignTransport` を局所版の境界で | `hTop_of_leaf3` | D.T-4 |
| 条件付きの run 局所の `hRead`/`hE` | `rootEnv_of_run`、`counterLoop_final3L` | DG-DATAOF/COVER/ENV、C.EN-4 |

これらは**条件付きの接続**で、下の仮説が残る間は「閉じた経路」ではない。

残る仮説（台帳は FG 75 / T1 57 のまま）:

| 仮説 | 内容 | FG の行 |
|---|---|---|
| `Laws L` | runtime laws（明示引数） | A.P-02 |
| `hstart : Start L mctx cctx w` | 最外の呼び出しの開始（`AdmCtx`、`JQC 0`） | A.P-02 |
| `hr` | compile が成功した（前件） | A.P-04 |
| `hdRun` | run 局所の機械境界（旧 `hA6`/h_A_P06 の局所形） | h_A_P06 |
| `hRead`, `hE`（`final3`）または `hsnap`, `hquote`, `hreader`（`final3L`） | 環境の `X`・読み取り関数の出力 | DG-DATAOF/COVER/ENV、C.EN-4 / ENV cache |

他の 3 root（shift4Loop、counterEnableLoop、arbiterSignal）の `X_final` は不変（`hsrc`/`htr`/`hA6` が前提に残る）。`fgCircuit_of_H` の入力（未証明の H）は変更なし。

### 11.6 次の束

(1) `hdRun`（MachineDefinesRun）の供給: `synthesizeFromConst` が読む `ci`/`envR`/`envR'` が run の開始環境と一致すること（`RunSnap`）と、entry constant の 3 事実の関係を run の外から示せるか。(2) `RunReader` を kernel で扱える形（`partial` helper の外出し）にするか MetaM 検査器として固定するか。(3) 他 3 root へ同形の `…R` 連鎖と `hsrc`。

## 12. S1g（Issue `sparkle-fg-circuit-pilot` の次の束）: hdRun の供給、run の存在、他 3 root

土台 `4948898c`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回だけ）: `Tools/ShippingFGCircuitLinked.lean`、`Tools/ShippingFGCircuitLinked2.lean`、`Tools/ShippingFGCircuitFinal4.lean`、`Tools/ShippingFGCircuitRoots4.lean`、`Tests/Gen5/FGCircuitPilotCheck6.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT6 AXIOMS`: 36 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではなく、下のどの接続も「閉じた経路」ではない。

### 12.1 作業 1: `hdRun`（MachineDefinesRun）の供給

**S1f の `MachineDefinesRun` は供給の足場にならない**（訂正）。その `w1`（getConstInfo）、`w5`（最初の getEnv）、`w3`（run 本体の開始）は、`RunsTo` の式を満たす任意の world で、run の連鎖に結ばれていない。値 `ci`/`envR` を固定するだけなので、連鎖で伝わる性質（`ReadsAt`）から導けない。そこで連鎖に結んだ形を作った。

- `MachineDefinesLinked`（`Tools/ShippingFGCircuitLinked.lean`）: `core_chain` の連鎖 `w --coreHead--> w1 --getConstInfo--> w2 --getEnv--> w3 --synthesizeFromConst（その最初の getEnv は w3）-->` について、同じ 3 事実（`certifiedShape?` = none、`mixedCertifiedShape?` = none、`machineShape? = some shape`）を要求する。消費側（`machine_run_of_coreC`、`machineRunJQC_of_closesC`、`synthesizeCombinationalCore_machine_soundC`）は `core_chain` で分解する写し（`…R` の証明の写し）。endpoint 連鎖は `Linked2.lean`（`RunLocal2` の機械的な写し。`MachineDefinesRun` → `MachineDefinesLinked`、名前の `R` → `C`）。`hTop_of_leaf4`、`counterLoop_artifact_atC`、`counterLoop_final4D` は `Final4.lean`。
- **供給**: `machineDefinesLinked_of_env`。既存の machineDefines の補題（`machineDefines_at_chain` / `machineDefinesR_of_env` / `readsSupply_of_quiet`）の形を run 局所に写した。前提は `Start`（`AdmCtx` と `JQ 0`）、`hquiet : ∀ u, L.O.quiet u → ReadsAt e cref u`（DG-ENV の quiet 強化。単一の `L` に対する前提として置いた）、`GetEnvFrame`（`getEnv` の枠の法則）、環境 `e` の事実（`e.find? X`、2 つの拒否、`machineShape?`）。既存の `readsSupply_of_quiet` は 2 つ目の `getEnv` の存在を前提に取るので、そのまま使わず `envR'` を要求しない形で書き直した。
- **`counterLoop_final4`**: 仮説は `L lvl hstart hr hquiet hg hgates hRead hE`。`hdRun` は無い（`machineDefinesLinked_of_reader` で導く）。`hgates : EntryGates (envAt cref w) X` は、`entry₀ env X` が `certifiedShape?`/`mixedCertifiedShape?` で拒否されるという**開始環境 1 個の事実**（第 3 の事実 `machineShape?` は `RootReader` の連言）。`counterLoop_final4D` は linked 境界を仮説に持つ版。

**導けない部分（何が要るか）**:

| 前提 | 内容 | 要るもの | FG の行 |
|---|---|---|---|
| `hquiet` | quiet な world はどれも開始環境と同じ導出引数（`instancePredicate`/`userInliner`/`structEnv`）を持つ | `O.quiet` は `Laws L` の不透明な述語。DG-ENV の `L'`（`QuietStrength`）を `L` に取り込む行が要る | C.EN-4 / ENV |
| `GetEnvFrame` | `getEnv` が Core 状態の環境を変えない | `ST.Ref.get` は `@[extern] opaque`。`CellPrem`（C.EN-4）の `ReadWorld` 等から `EnvFrameEnd` は出る（`ShippingGen5EnvFrame3`）が、`GetEnvFrame` との接続は確認していない | C.EN-4 |
| `hgates` | 入口定数の 2 つの拒否 | `entryConst` は `userInliner env`/`instancePredicate env` に依る。`ci` 部分だけなら決まるが、`inlinedConst inl ci` は抽象環境では kernel で評価できない。環境 1 個の値としては SNAPSHOT6 で確認 | h_A_P06（env 水準） |

### 12.2 作業 2: run から出る事実と、残る名前付き前提

- `root_find_of_run`: run の連鎖の `getConstInfo X` の world は `ReadsAt (envAt cref w)` を持つので、`X` は開始環境の定数（`hE` の**存在**の部分。`hquiet` だけで出る。`QuoteFact` は不要）。
- `QuoteAt`（定数の内容が引用と一致。条件は上の lookup）と `ReaderAt`（入口定数に対する `machineShape?` と `dataOfAt` の結果）を、lookup を条件とする名前付き前提にした。`rootEnv_of_lookup` で `RootInEnv` と `RootReader` が出る。`counterLoop_final5` の仮説は `L lvl hstart hr hquiet hg hgates hquote hreader`。
- S1f の `RunSnap`（3 つの読み取り world の環境が**等しい**）は不要になった。連鎖で伝わる弱い `ReadsAt`（find? の包含 + 3 導出引数の等号）で足りる。`RunQuote` の「`ci` が `defnInfo`」は `QuoteAt`、`RunReader` は `ReaderAt`。
- **供給できていないもの**: `QuoteAt`（C.EN-4 の `QuoteFact`、ENV cache）、`ReaderAt` の `dataOfAt` の結果（`partial` の helper を呼ぶ。DG-DATAOF / DG-COVER / DG-ENV）。`machineShape?` の結果は `ReaderAt` に残る。

### 12.3 作業 3: 他の 3 root

4 root とも `LeafFacts`（`decide`）が成り立つ（arbiterSignal も `insts = []` の register leaf）ので、`DesignTransport` は `designTransport_of_leaf` の経路で 4 root とも供給される。**この束には leaf でない root は無い**。

- `hsrc`（D.D-3）: `src_eq_of_states`（`counterLoop_src_eq` の一般形。root 固有の項を使わない）、`loop_states`（`Signal.loop` の状態列。`truncLoop` で切った生き信号を使う）、`hst_of_loop`、`hsrc_of_states` を作り、`shift4Loop_hsrc`（レジスタ列: `machine_reset`/`machine_writes`/`machine_result`）、`counterEnableLoop_hsrc` と `arbiterSignal_hsrc`（`Signal.loop`: `machine_reset`/`machine_writes`/`machine_result`/`machine_source`。arbiter は `DomainConfig` 多相のまま）を kernel で供給した。仮説は `RootReader` のみ。
- 各 root の `X_final4`（`machine_traceL_of_regsC` を `shift4Loop` 用に追加）と `X_final5`: counterLoop と同じ形。arbiterSignal は `hB : BoundaryRowsInEnv` が残る。
- 非 leaf の root が来た場合に要るもの（今回は適用なし）: `NoRawBelow` と lookup の一致（`Tools/ShippingGen5DCEntryT.lean` の `childMap_transport`、`runModuleTG_transport`）、`hsrc` は呼び出し stage（`ExtStage`）に対する帰納、`DesignTransport` は instance の oracle を通る。

### 12.4 Check6 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck6`、893 jobs、exit 0）

- `FGCIRCUIT6 SIGNATURES`: `MachineDefinesLinked`、`machineDefinesLinked_of_env`、`root_find_of_run`、`rootEnv_of_lookup`、`X_final4`/`X_final5`（4 root）、`X_hsrc`（3 root）の期待型を**型全体**で独立に書いて `isDefEq` で照合。mutant（premise の環境、root の design、shape/data、`Start`/`hr`/`hquiet`/`GetEnvFrame`/`hgates` の欠落、旧 `MachineDefines`/`hsrc`/`hdRun` の追加、world の結び 3 種、flag、名前、root 間の入れ替え）を棄却。
- `FGCIRCUIT6 HYPS` / `REMAINING`: 全 final 定理の仮説名と型。`hw`・`ReflectsAll`・`hA6`・全 world の `MachineDefines`・`MachineDefinesRun`/`Linked`・`hsrc`・`DesignTransport` は仮説に無い。
- `FGCIRCUIT6 AXIOMS`: 36 名、標準 axiom のみ。
- `FGCIRCUIT6 SNAPSHOT6`: この build の環境 1 個で、4 root それぞれについて `EntryGates`（2 つの拒否）、`machineShape?`、`dataOfAt`（fuel 1000000）の結果が endpoint の `machineData` と全構造で一致し、10 個の 1 フィールド摂動と他 root のデータを棄却。**環境 1 個の値**で、任意の run についての `hquiet`/`hgates`/`hRead` の kernel の文ではなく、全前提が同時に満たされる例でもない（`Laws`・run・`Environment` の閉じた項は作っていない）。
- `FGCIRCUIT6 STREAMS`: **別種の証拠**。kernel が `counterLoop.val 0 = 0`、`counterLoop.val 3 = 3`、`shift4Loop (pure 5)` の `val 3 = 0`、`val 4 = 5` を証明する（観測 0/3 の形）。`hsrc` が `p.src` と等しいとする観測が自明な流れでないことを示すだけで、前提の充足とは無関係。

### 12.5 root ごとの状況と残る仮説（FG の行 ID）

| root | 閉じたもの（条件付き） | 残る仮説 |
|---|---|---|
| counterLoop | `hdRun` 消去（final4）、`hsrc`、leaf `DesignTransport`、`Start`+`hr`、final5 | `Laws L`・`hstart`（A.P-02）、`hr`（A.P-04）、`hquiet`+`GetEnvFrame`（C.EN-4/ENV）、`hgates`（h_A_P06 の env 水準）、`hRead`/`hE`（final4）または `hreader`/`hquote`（final5。DG-DATAOF/COVER/ENV、C.EN-4 QuoteFact） |
| shift4Loop | 同上（レジスタ列の `hsrc`） | 同上 |
| counterEnableLoop | 同上（`Signal.loop` の `hsrc`） | 同上 |
| arbiterSignal | 同上（`DomainConfig` 多相の `hsrc`） | 同上 + `hB`（`BoundaryRowsInEnv`: ENV） |

`fgCircuit_of_H` の入力（未証明の H）は変更なし。

### 12.6 次の束

(1) `hquiet`/`GetEnvFrame` と `CellPrem`（C.EN-4）の接続（`GetEnvFrame` を `CellPrem` から導けるか、`L'` の取り込み方）。(2) `hgates` を env 水準の決定可能な検査器にするか、`inlinedConst` の性質から出すか。(3) `QuoteAt`/`ReaderAt` の供給（`partial` helper の外出し、または MetaM 検査器として固定）。(4) 非 leaf の root への持ち上げ。

## 13. S1h（Issue `sparkle-fg-circuit-pilot` の次の束）: hquiet/GetEnvFrame の接続、hgates の検査器、QuoteAt/ReaderAt の移送、非 leaf root の調査

土台 `74d5ca1d`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回）: `Tools/ShippingFGCircuitS1hFrame.lean`、`Tools/ShippingFGCircuitS1hGates.lean`、`Tools/ShippingFGCircuitS1hQuote.lean`、`Tests/Gen5/FGCircuitPilotCheck7.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT7 AXIOMS`: 19 名、標準 axiom のみ）。`MachineDefinesLinked` の定義は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。

### 13.1 作業 1: hquiet / GetEnvFrame と CellPrem（C.EN-4）

- **`GetEnvFrame` は独立の前提ではなくなった**: `getEnvFrame_of_readWorld : ReadWorld cref → GetEnvFrame`（`CellPrem` の成分 `hc`。`getEnvFrame_of_cellPrem` は `CellPrem` 全体から）。`envFrame_of_envFrameEnd` は `EnvFrameEnd`（`endW` 形）から `RunsTo` 形への一般補題。
- **`hquiet` は CellPrem から導けない**: `hquiet : ∀ u, L.O.quiet u → ReadsAt e cref u` は不透明な述語 `L.O.quiet` の全称で、`CellPrem` に現れない。`hquiet_of_strength` は `QuietStrength L L' e` の `→` 向きが `L'` に対する `hquiet` そのものであることを示すだけ（構成済みの `L'` が要る）。
- **証明が使っていたのは 1 点だけ**: run の連鎖の `coreHead` の後の world `w1` で `ReadsAt (envAt cref w) cref w1`。これは開始 world で自明（`readsAt_self`）で、`EnvFrame (coreHead X)`（1 つの MetaM 動作の環境枠）から出る（`readsAt_after_head`）。そこで `machineDefinesLinked_of_head`、`root_find_of_head`、`machineDefinesLinked_of_reader_head`、`counterLoop_final6` は `hquiet` と `GetEnvFrame` の代わりに `hhead : EnvFrame (coreHead X)` と `hcell : ReadWorld cref` を取る。
- **残る**: `hhead`。`coreHead` は `IO.getEnv`・（`SPARKLE_PROFILE` 時の）ファイル IO・`sparkleSynthDepth.get`/`sparkleFvarValueMap.get` を実行する。ref の get は `CellOK`（`CellPrem`）で足りるが、IO 動作は class-D の `ioEnv` 行（`DRow`、U3 で未供給）で、「IO 動作は `cref` のセルを変えない」法則が要る。`ReadWorld cref` 自体も `CellPrem` の成分（実ランタイムでは前提）。

### 13.2 作業 2: hgates の検査器

`entryGatesB (env) (X) : Bool`（`Tools/ShippingFGCircuitS1hGates.lean`）は `entry₀ env X` を引き、`certifiedShape? = none` と `mixedCertifiedShape? = none` の 2 つの `isNone` を検査するだけ。`entryGatesB_sound`（true ⇒ `EntryGates`）、`entryGatesB_complete`、`entryGatesB_iff`、`not_entryGates_of_false`。意味保存を Bool の名前に置き換えていない（`EntryGates` の 2 条件そのもの）。`counterLoop_final7` は `hgates` を `entryGatesB (envAt cref w) X = true` に替えた。
`Environment` は閉じた kernel 項ではないので `decide` では評価できない。4 root の評価は、コンパイル済みの関数を MetaM で走らせる（Check7 の SNAPSHOT7: 4 root で `true`、certified な組合せ回路の対照 `combControl` で `false`）。これは**環境 1 個の値**で、任意の run の開始環境についての kernel の文ではない。

### 13.3 作業 3: QuoteAt / ReaderAt の供給

`dataOfAt`・`machineShape?` は `partial` helper を呼び、`MachineData` は `Lean.Expr` を含み（`Expr.eqv` は extern）、健全な Bool 等価検査器は、現在の方式では未実装（不可能性は証明していない）。kernel でできる範囲として、これらの事実が環境に依るのは `find? X`・`instancePredicate`・`userInliner`・`structEnv` だけであることを使った移送を供給した（`Tools/ShippingFGCircuitS1hQuote.lean`）: `ReadsAt env₀ cref w`（開始 world が `env₀` を読む）と、開始環境に root がある（run から出る: `root_find_of_head`）ことから、`entryGatesB`・`QuoteAt`・`ReaderAt` が `env₀` から開始環境へ移る（`entryGatesB_of_readsAt`、`quoteAt_of_readsAt`、`readerAt_of_readsAt`）。`counterLoop_final8` の前提は `L lvl env₀ hstart hr hhead hcell hread hgatesB hquote hreader`。
減ったもの: 「任意の run の開始環境についての 3 つの評価の文」が、「1 つの検査済み環境 `env₀` についての同じ 3 つの文（MetaM で確認する）」と「環境の同定 `ReadsAt env₀ cref w`（DG-ENV C0）」に分かれた。残るもの（FG の行 ID）: `QuoteAt env₀`（C.EN-4 `QuoteFact`）、`ReaderAt env₀`（DG-DATAOF/COVER/ENV）、`ReadsAt env₀ cref w`（DG-ENV C0）。`env₀` が具体環境であること（kernel の閉じた項としての供給）は、現在の方式では未供給（不可能性は証明していない）。snapshot は 1 つの env、`lvl = (fun _ => 1000000)` での評価で、任意の `lvl` についての `ReaderAt` の供給ではない。

### 13.4 作業 4: 非 leaf の root

選んだ root: **`synth_hftPcieOutByte`**（`Tests/IP/Bus/PCIeHFTTest.lean:89`、S0 一覧の Tests/IP/Bus。`hftPcieLoop`（`IP/Bus/PCIeHFT.lean`）を包む）。プローブ（`kjob lake env lean`、build 済み環境）: `certifiedShape?` = none、`mixedCertifiedShape?` = none、`machineShape?` = some（insts = [`Sparkle.IP.Net.HTTP.httpGetByte`, `Sparkle.IP.Bus.PCIe.tlpCplByte`]、slots 17、runs 3、loops 0）。つまり machine 経路で、`EntryGates` 型の条件は S1 の経路にそのまま乗る。`Examples/HierarchicalCPU` の `twoStageAdder` は組合せ回路で machine 経路ではないため選ばなかった。
足りないもの（読んだ範囲。未ビルド・未検証の調査）:
1. `LeafFacts` は `insts = []` を含み、`leaf_topShips_of_run`（Bridge:50 と Final3/Final4 の写し）、`leaf_instFree_of_run`、`designTransport_of_leaf`、`hTop_of_leaf2/3/4`、`genGP_root`/`genGP_root_canon`（Cover）、`src_eq_of_states`（`ExtStage … 0 = id`）、`machine_ships_wiredC` の `hnoI`/`hsl`/`hSS` が leaf 専用。`hTop` には `TopShips`/`ChildShips`（Gen2Defs）を使う非 leaf の経路（`StepStmt`、`t1_of_stepPF_ND`、`T1Stmt`）があるが、具体 root に対する `StepStmt` の無条件の証明は見つかっていない。大。
2. 子 2 個（`@[hardware_module]`）の各 package（`genGP` の `Acc (CallRel K) X` を子の行を通した整礎性で）、子ごとの `RootReader`/`machine_closes`/`MachineDefines`、`ResetNk`。
3. `hsrc`: `ExtStage` に対する帰納と子の package `src` の再帰（`loop_states`/`hsrc_of_states` は状態列部分で再利用できる見込み）。中〜大。
4. `DesignTransport`: `childMap_transport`/`runModuleTG_transport`（`Tools/ShippingGen5DCEntryT.lean`）に `NoRawBelow` と lookup 一致が要る。中。
5. 機械の endpoint 定理（`machine_*`、`machineData`）が `synth_hftPcieOutByte` に対して生成されるか、`insts` 付きの shape で `dataOfAt` が正しいデータを返すかは未確認（SNAPSHOT 型の MetaM 検査が要る）。`MachineDefinesLinked`・`EntryGates`・`QuoteAt`/`ReaderAt`・`root_find_of_head` は `insts` に依らない形。
実装は次の束。

### 13.5 Check7 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck7`、897 jobs、exit 0）

- `FGCIRCUIT7 SIGNATURES`: `getEnvFrame_of_readWorld`、`machineDefinesLinked_of_head`、`root_find_of_head`、`counterLoop_final6/7/8`、`entryGatesB_sound/complete`、`entryGatesB_of_readsAt`、`quoteAt_of_readsAt`、`readerAt_of_readsAt` の完全な期待型を独立に書いて `isDefEq`（default 透過度。`match` 補助関数の違いを吸収するため）で照合。40 mutant 棄却（検査ごとに数える。以前の 41 は sound/transfer の 7 件に 8 を足した数え間違い。`isDefEq` は default 透過度で whitelist 以外の定義も展開しうるので、「whitelist だけを展開する」とは言わない。他 root の head 枠、end world の `ReadsAt`＝別の run の world、head/cell/read 前提の欠落、別の env / root / Post / data、移送の逆向き、検査器と命題の取り違え）。
- `FGCIRCUIT7 HYPS`/`REMAINING`: final6/7/8 の仮説名と型。`hquiet`（quiet 述語の全称）・`GetEnvFrame`・`hw`・`hA6`・`MachineDefines*`・`hsrc`・`hdRun`・`DesignTransport` は仮説に無いことを検査。
- `FGCIRCUIT7 AXIOMS`: 19 名、標準 axiom のみ。
- `FGCIRCUIT7 SNAPSHOT7`: 上のとおり、環境 1 個の値（4 root で `entryGatesB` = true、quote が pilot の定数と一致、SNAPSHOT6 を再実行、対照で false）。全前提が同時に成り立つ例ではない。

### 13.6 残る仮説（counterLoop_final8 の形）と次の束

`Laws L`・`hstart`（A.P-02）、`hr`（A.P-04）、`hhead`（C.EN-4: IO 動作の環境枠）、`hcell : ReadWorld cref`（C.EN-4 CellPrem）、`hread : ReadsAt env₀ cref w`（DG-ENV C0）、`hgatesB`（h_A_P06 env 水準）、`hquote`（C.EN-4 QuoteFact）、`hreader`（DG-DATAOF/COVER/ENV）。他 3 root への final6〜8 の持ち上げは機械的（未実施）。次: `hhead` の IO 枠法則、`env₀` の具体化の仕方、非 leaf root（§13.4 の 1〜5）。

## 14. S1i（Issue `sparkle-fg-circuit-pilot` の次の束）: hhead の導出、CheckedStart、4 root への持ち上げ、非 leaf の一歩

土台 `a4c6e62d`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は最初の commit で 1 回）: `Tools/ShippingFGCircuitS1iHead.lean`、`S1iEnv.lean`、`S1iRoots.lean`、`S1iChild.lean`、`Tests/Gen5/FGCircuitPilotCheck8.lean`。TRUSTED・axiom・sorry・native_decide はない（`FGCIRCUIT8 AXIOMS`: 27 名、標準 axiom のみ）。`MachineDefinesLinked` と `Laws` は変えていない。新しい law は足していない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は**条件付き**で、下のどの接続も「閉じた経路」ではない。

### 14.1 作業 1: hhead（`EnvFrame (coreHead X)`）

`coreHead X` は一直線の MetaM 動作: `IO.getEnv "SPARKLE_PROFILE"`、（変数があるときだけ）stderr とファイルへのログ IO、副キャッシュ（`SideRef`）と `sparkleSynthDepth`/`sparkleChildCache` の `ST.Ref.get/set`、深さ制限の `throwError`。
- **導けた部分**: `envFrame_coreHead X (hcell : CellPrem MkRefd mref cref) (hio : HeadIO …) : EnvFrame (coreHead X)`。`ST.Ref` の get/set と `throwError` は `CellPrem`（`ReadWorld` と `CellOK`）から出る（join point を含む do ブロック全体を、構文に沿った小さな tactic `ef_step` で分解。`letFun`/`ite`/`bind`/`pure`/get/set/throwError の 7 種）。
- **現時点で供給経路が見つかっていない部分 = `HeadIO`（2件のIO動作の義務）**: (1) `EnvFrame (liftM (IO.getEnv "SPARKLE_PROFILE"))`、(2) `∀ msg, EnvFrame (liftM (profLogIO true msg))`（`profLogIO false` は `pure ()` として証明済み）。足りないもの: 既存の法則はどれも IO 動作の `envAt cref` を語らない。`Laws` の `frame`/`frameQ`/`same`（`FramedA.ioEnv`）は `cv`/`sv`/`dv`/quiet だけ、`QuietStrength` は強化した `L'` の連言として `ReadsAt` を足すだけで、`frameQ_plus` は class-D の行（`DRow.ioEnv`）を `¬ DRow p` で除外している。`ReadWorld` は `ST.Ref` の get の法則。つまり「IO.getEnv とログ IO は `cref` のセルを変えない」は、(1) は `IO.getEnv` 1 件、(2) は profile ログ（複数の IO 動作の合成。「2 個の primitive」ではない）についての義務で、`Laws`/`CellPrem`/`QuietStrength`/`ReadWorld` からは**供給経路が今のところ見つかっていない**（導出不能の証明はない）。
- **最小の形**: `HeadAt X mctx mref cctx cref w`（`coreHead` の run が開始 world `w` から到達する world だけ: `∀ s w1, RunsTo (coreHead X) … w s w1 → envAt cref w1 = envAt cref w`）。`headAt_of_frame`（`EnvFrame` から）、`headAt_of_cellPrem`（`CellPrem` + `HeadIO` から）。`readsAt_after_headAt`、`root_find_of_headAt`、`machineDefinesLinked_of_headAt`/`_of_reader_headAt`、`counterLoop_final9`（final8 の `hhead : EnvFrame` を `HeadAt X w` に）、`counterLoop_final9C`（`CellPrem` + `HeadIO` から）。
- 減ったもの: 全 world の `EnvFrame (coreHead X)` が、run の開始 world 1 点の `HeadAt`、あるいは（`CellPrem` が供給される前提で）2件のIO動作の義務（`HeadIO`）になった。`hr` は前件のまま。

### 14.2 作業 2: `CheckedStart`（env₀ と開始環境を 1 つの名前付き前提に）

- `CheckedEnv lvl env₀ X ty val dd`: `root : ∃ d, RootInEnv env₀ X ty val d`（**型の上の文**: `env₀.find? X = some (.defnInfo d)`、`d.levelParams = []`、`d.type = ty`、`d.value = val`。`ty`/`val` は宣言の閉じた kernel 項）、`gates : entryGatesB env₀ X = true`、`reader : ReaderAt lvl env₀ X dd`。
- `CheckedStart lvl env₀ cref w X ty val dd`: `CheckedEnv` + `link : ReadsAt env₀ cref w`（DG-ENV C0）。`startFacts_of_checked`: run が供給する lookup（`root_find_of_headAt`）とあわせて、開始環境の `EntryGates`、`RootInEnv`、`RootReader` が出る。`quoteAt_of_rootInEnv`（`QuoteAt` は `root` から）。
- **型の上で示せる範囲**: `entry₀_of_rootInEnv`、`entryGatesB_of_rootInEnv`: `root` があれば `env₀` の入口定数は `entryConst true false [] (.defnInfo d) (instancePredicate env₀) (userInliner env₀) (structEnv env₀)` で、ゲート検査器はこの項への 2 つの `isNone` 検査である。つまり `gates` と `reader` が `env₀` に依るのは、閉じた宣言 `d` のほかは `ReadsAt` が等しいとする 3 つの導出引数だけ。**評価が要る部分**: `certifiedShape?`/`mixedCertifiedShape?`/`machineShape?`/`dataOfAt` の値（`userInliner` は環境を展開し、`dataOfAt` は `partial` helper。`Environment` は閉じた kernel 項でない）。これは MetaM の評価（SNAPSHOT8a）で、前提の供給とは数えない。
- 現在の方式では `Environment` の値を kernel の閉じた項として供給していない（未供給。`mkEmptyEnvironment` は IO で、不可能性の証明はない）。したがって今の範囲は、`root` の型の上の文と、評価した 1 環境の値（SNAPSHOT8: 1 つの env、`lvl = (fun _ => 1000000)` での評価）までで、任意の `lvl` についての `ReaderAt` の供給ではない。

### 14.3 作業 3: 他の 3 root

`X_final4D`（S1g の `X_final4` から `hquiet`/`GetEnvFrame` を作る 2 行を除き、`hdRun` を仮説に取る形。証明は S1g のコピー）と、`X_final10`（4 root: `counterLoop_final10`、`shift4Loop_final10`、`counterEnableLoop_final10`、`arbiterSignal_final10`）。仮説は `L lvl env₀ hstart hr hhead(HeadAt) hcell(ReadWorld cref) hchk(CheckedStart)`。final6〜8 の形が 4 root で揃った。
- **arbiter の `hB`**: `BoundaryRowsInEnv (envAt cref w)` は 3 つの補助定数が開始環境に**存在する**という文で、`ReadsAt` は一方向（開始 ⊆ env₀）なので移送できない。そこで逆向きの包含を 3 つの名前に限った名前付き前提 `ContainsAt env₀ cref w boundaryNames` を足し、`BoundaryRowsInEnv env₀`（1 環境の文。MetaM で評価）から `boundaryRows_of_contains` で `hB` を出す。`arbiterSignal_final10` の追加仮説は `hB0 hcont`。`hB` を `ReadsAt` の形に**そのままは寄せられない**（positive な存在を `ReadsAt` は運ばない）。

### 14.4 作業 4: 非 leaf の root（`synth_hftPcieOutByte`）

- 実装: `topShips_transport`（`S1iChild.lean`）: `TopShips p n X b raw D → TopShips p n X b raw D'` を、`PostEntry b raw D D'`、`NoRawBelow D raw.name (n+1) raw`、`NoRawBelow D raw.name (n+1) (checkedOptimize b)`、「`b.body` の instance は top を指さない」から導く。既存の `resetNk_transport`、`runModuleTG_transport`、`postEntry_lookup_ne` を使い、新しいのは `TopShips` への持ち上げと `bodyInstOuts_congr`。`designTransport_of_noRawBelow`（`DesignTransport` の形）。計算できる検査器 `noRawBelowB`（`noRawBelowB_sound`）と `instsNeB`（`instsNeB_sound`）で、側条件を実際の出力で評価できる。
- leaf の補題で済まないもの（実装で確かめた）: `topShips_design_irrel`/`designTransport_of_leaf` は `raw`/`b`/`checkedOptimize b` が instance-free であることで設計 `D` を無視する。instance があると `TopShips` は `childMap D.modules`、`ResetNk n raw D kids`、`bodyInstOuts (childMap D.modules) b.body` を通して `D` を読む。`D' = topMap … D` は top（`raw.name`）だけを置き換えるので、移送は「top を指す instance が下にない」（`NoRawBelow`）に帰着する。この文は `raw`/`b` の中身（instance の targets）についての事実で、leaf では機械 trace から instFree を読んだ（`leaf_instFree_of_run`）が、非 leaf では**読む補題が今のところ見つかっていない**ので、`topShips_transport` の仮説として残る。`NoRawBelow` は「top に戻らない」条件で、グラフ全体の非巡回性は十分条件の一候補にすぎず、必須とは言わない。`designTransport_of_noRawBelow` は**全 n** の `NoRawBelow` を要求し、SNAPSHOT8b の深さ 1〜6 の評価はそれを供給しない。
- SNAPSHOT8b（**プローブ `hftOutProbe`**＝`(hftPcieLoop ..).outByte` の compile。private な `synth_hftPcieOutByte` 自身ではない。S1l で記録訂正）: machine 経路（certified none、mixed none、`machineShape?` some、insts 2、slots 17）。raw の instance は `httpGetByte` と `tlpCplByte`、`D₀`/`D'` の modules は等しい（top は含まれない）、`raw` は `synthesizeCombinationalCore`、`b`/`D'` は外側の `synthesizeCombinational` の**別々の 2 回の実行**で、比べたもの。PostEntry は `dropZeroWidth` **または** `mergeChecked` の選言で、どちらの枝が成り立ったかは Check8 が計算してログに出す（S1l）。同一 run の PostEntry の証拠とは数えない。`noRawBelowB` は raw と `checkedOptimize b` で深さ 1〜6 すべて true、`instsNeB` true。対照（子を top に見立てる）は false。これは**プローブの 2 回の実行の値**で、任意の run の kernel の文ではない。
- `CheckedStart`（root/gates/reader/link を 1 つの binder に束ねたもの）は束ねただけで、前提の**減算ではない**（台帳に数えない）。
- 残る（未実装）: (1) `TopShips p n X b raw D` 自体（machine 経路で `insts ≠ []`。`LeafFacts` が leaf 専用）、`NoRawBelow` を run から出す補題（instance の module 名の分離。非巡回性は十分条件の一候補で必須とは断言しない）。(2) 子ごとの package（`genGP` の `Acc (CallRel K) X`）、`RootReader`/`machine_closes`/`MachineDefines`。(3) `hsrc`: `src_eq_of_states` は `ExtStage … 0 = id`（`insts = []`）を使う。非 leaf は `ExtStage … k` を子の package の `src` に結ぶ帰納が要る（`ShippingGen5SemExt` の `calleeOut`/`ExtStage_succ` が材料）。(4) `machineData` が `insts` 付きで正しいか（`dataOfAt` の評価）。

### 14.5 Check8 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck8`、909 jobs、exit 0）

- `FGCIRCUIT8 SIGNATURES`（66 mutant。head/ReadsAt/CheckedStart の「end world」対照は**同じ run の終点 w'** で、MDLBODY の独立 world `u` 対照とは別物）: `envFrame_coreHead`、`root_find_of_headAt`、`machineDefinesLinked_of_headAt`、`counterLoop_final9`/`9C`、`CheckedEnv.mk`、`CheckedStart.mk`、`HeadIO.mk`、`startFacts_of_checked`、4 root の `X_final10`、`boundaryRows_of_contains`、`topShips_transport`、`noRawBelowB_sound`、`instsNeB_sound` の完全型（仮説・結論・binder の種類）を独立に書いて `isDefEq` で照合。66 mutant 棄却: 別の root の head、同じ run の終点（end world w'）での head / `ReadsAt` / `CheckedStart`、接続を切ったもの（head 事実・cell・IO 事実・link・`NoRawBelow` の欠落）、別の env / root / Post / data、別の root の final 定理、移送の逆向き。
- `FGCIRCUIT8 MDLBODY`（S1j、S1h 指摘 2）: `MachineDefinesLinked` の定義の本文の独立な写し `MDLBody` と一致することを確認した上で、本文を比べる対照 3 件を、SIGNATURES の 66 とは別に数えて棄却（3 mutant）: (a) 連鎖の前半（coreHead / getConstInfo / getEnv）の全削除、(b) `coreHead` の開始を独立した world `u` に替えたもの（独立 u 対照）、(c) 本文（`synthesizeFromConst`）の開始を独立した world `u` に替えたもの。
- `FGCIRCUIT8 HYPS` / `REMAINING`: 各 final の仮説名と型。`hquiet`・`GetEnvFrame`・全 world の `EnvFrame`・`hdRun`・`MachineDefinesLinked`・`hsrc`・`DesignTransport`・`hw` は仮説に無い。
- `FGCIRCUIT8 AXIOMS`: 27 名、標準 axiom のみ。
- `FGCIRCUIT8 SNAPSHOT8a/8b/8c`: 上のとおり（8b はプローブ `hftOutProbe` の 2 回の実行）。1 環境・プローブの実行の値で、全前提が同時に成り立つ例ではない。

### 14.6 残る仮説と次の束

4 root の final10 の仮説: `Laws L`・`hstart`（A.P-02）、`hr`（A.P-04）、`hhead : HeadAt`（C.EN-4: `coreHead` の IO 2 件の環境枠。`CellPrem` + `HeadIO` から）、`hcell : ReadWorld cref`（CellPrem）、`hchk : CheckedStart`（`root` = 型の文、`gates`/`reader` = 1 環境の評価、`link` = DG-ENV C0）、arbiter は `hB0`/`hcont`。
次: (1) `HeadIO` の 2 件（IO 枠）。(2) `reader`/`gates` の評価を kernel の文に（`dataOfAt` の `partial` helper の外出し）。(3) 非 leaf: `NoRawBelow` を run から出す補題と `TopShips` の machine 経路（insts 付き）、`hsrc` の `ExtStage` 帰納。

## 15. S1k（Issue `sparkle-fg-circuit-pilot` の次の束）: 非 leaf root `synth_hftPcieOutByte` の最終定理の型の固定と、証明できた部分

土台 `8b4c135b`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 lib 1 回）: `Tools/ShippingFGCircuitS1kRoot.lean`、`S1kStmt.lean`、`S1kPkg.lean`、`Tests/Gen5/FGCircuitPilotCheck9.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない（`FGCIRCUIT9 AXIOMS`: 12 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は**条件付き**で、閉じた経路ではない。Issue の状態は変えていない。
注: root は `Tests/IP/Bus/PCIeHFTTest.lean:89` の `private def` なので名前を指せない。同じ本体の公開版 `Tools.ShippingFGCircuitS1kRoot.synth_hftPcieOutByte` を新ファイルに置いた（Check8 の `hftOutProbe` と型・値が同一であることを SNAPSHOT9 で検査）。元の private 定義そのものについての定理ではない。

### 15.1 手順 1: プローブ（`kjob lake build Tools.ShippingFGCircuitS1kRoot`、exit 0）

- 子 2 個の endpoint は**既にある**: `httpGetByte`（`Tests/Compiler/ShippingMachineCombTest.lean` の `#machine_endpoint`）と `tlpCplByte`（今回 `#machine_endpoint` で生成。通った）。どちらも `machineData`/`machine_ok`/`machine_body`/`machine_closes`/`machine_sound`/`machine_ships`/`machine_ships_comb` を持つ。
- root は `#machine_endpoint` が通り、`machineData`/`machine_ok`/`machine_body`/`machine_sound` はあるが、**`machine_closes`・`machine_ships` は生成されない**（instance を持つ module には出ない。コマンドの設計）。root の closing は未供給。
- reader の接続: `dataOfAt`（fuel 1000000）は 3 宣言とも `machineData` リテラルと**全構造で等しい**値を返す（`dataExprOf d == literalExpr`）。root の `insts` = [`httpGetByte`, `tlpCplByte`]（2 個）、子は `insts = []`。3 宣言とも `entryGatesB` true、machine 経路（certified none、mixed none、`machineShape?` some）。1 環境の値であり、任意の run の kernel の文ではない。
- `CD`（`SourceDenotesMono` の核）には**利用者定義定数の適用規則も構造体射影の規則もない**。root の値 `fun … => HFTPcieOut.outByte (hftPcieLoop …)` に `CD` の導出を作れない（未供給。規則の追加は既存ファイルの変更）。

### 15.2 手順 2: 完全な型（`HftFinalStmt`、`synth_hftPcieOutByte_final : HftFinalStmt`）

`X_final10` と同じ結論 `(∃ raw, PostRun …) ∧ ∃ mm p, RootArtifactMono (envAt cref w) (genGP …) (PostRun …) root shHft mm b D' p` で、前提は:
`L lvl env₀`、`hstart`（A.P-02）、`hr`（A.P-04）、`hhead : HeadAt`（C.EN-4）、`hcell : ReadWorld cref`、`hchk : CheckedStart`（root の `machineData`、型 `hftRootType`・値 `hftRootValue`）に、**子の package の前提** `hreadH`/`hreadT : RootReader lvl (envAt cref w) child child.machineData`（DG-DATAOF/COVER/ENV）、**名前付きの 4 obligation**:

| 前提 | 内容 | FG 行 | 状態 |
|---|---|---|---|
| `hcd : HftObCD` | `CD [] hftRootValue (MonoTy shHft) synth_hftPcieOutByte` | D.D-1 / D.D-4（`CircCV`） | 未供給（`CD` に規則がない） |
| `hsrc : HftObSrc` | `genGP` が返す package の `src` が宣言の観測 | D.D-3 / DG-SEM | 未実装（`ExtStage … 2` を子の package の `src` に結ぶ帰納。`src_eq_of_states` は `ExtStage … 0 = id`） |
| `htop : ∀ p, genGP … = some p → HftObTopCore …` | run の `raw` が核の設計 `D₀` で `TopShips p n`（`hdRun` を前提に取る） | D.D-4（T1 の machine 経路、insts 付き） | 未実装（`LeafFacts` は leaf 専用。子の package と `ChildShips`） |
| `hnoraw : HftObNoRaw` | `raw`/`checkedOptimize b`/`b` の instance が top を指さない | D.T-4 | 未実装（run から出す補題がない。1 回の compile では `noRawBelowB` が true: Check8 SNAPSHOT8b） |

`hdRun`（`MachineDefinesLinked`）は前提ではなく、`hchk`/`hhead`/`hcell` から導出して `htop` に渡す。`hgates`/`hRead`/`hE` も `hchk` から出る。`hsrc`・`hcd` は root 固有の文、`htop`/`hnoraw` は run についての文。

### 15.3 手順 3: 証明した部分

- `genGP_root_kids`（`genGP_root` の一般化）: root の callee が全て table の leaf 行なら `genGP … root = some p`、`p.decl = root`、`p.d = g.d`、`p.kD = kDOf g.d`（`Acc (CallRel K) root` を子の leaf 行から、`genS_leaf_isSome`）。
- kernel の事実（`decide +kernel`）: 3 宣言の `GenWF`、子の `insts = []`、root の `insts.map (·.1) = [httpGetByte, tlpCplByte]`、`kDOf = 5`、`ShapeMatchesMono shHft … 5`、`monoGo [] hftRootType = some shHft`。
- `synth_hftPcieOutByte_final`: 上の 4 obligation と子の reader から、`genGP` の被覆・`EndpointLink`・`SourceDenotesMono`（`RootInEnv` + `hcd`）・`ObservationsEqualMono`・`HasConcretePackage`（`htop` + `hnoraw` から `topShips_transport` で `D'` へ）を導く。**`DesignTransport` は前提でなく証明**になった（`hnoraw` が前提）。
- 証明していない（上表の 4 件）。子の `MachineDefines`/`closes`、`ResetNk` は `htop` の中身として残る。

### 15.4 Check9 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck9`、916 jobs、exit 0）

- `FGCIRCUIT9 SIGNATURES`: 最終定理と `HftFinalStmt` の完全な型、4 obligation、root の kernel 事実、`genGP_root_kids` を独立に書いた文面と `isDefEq`（default 透過度）で照合。**41 mutant 棄却**（検査ごとに数える: 最終定理と `HftFinalStmt` の各 14 = 28、`HftObCD` 1、他の 3 obligation 4、kernel 事実 7、`genGP_root_kids` 1）: run の root / head / post が別、`hchk` が別宣言の data、head・cell・子 reader・4 obligation の各欠落、core obligation の `hdRun` 欠落、子 reader や結論が end world、instance 順の入れ替え、`kD = 4`、別の shape、callee 欠落、`TopShips` を印刷後の設計で述べたもの。注: `GenWF d = true` のように両辺が評価で `true` になる命題は `isDefEq` が同一視するため、wf/leaf の対照は偽の文（`= false`、`≠ []`）にした。
- `FGCIRCUIT9 HYPS`/`REMAINING`: 前提名 `L lvl env₀ hstart hr hhead hcell hchk hreadH hreadT hcd hsrc htop hnoraw` と型。`hquiet`・`GetEnvFrame`・全 world の `EnvFrame`・`hdRun`・`hgates`/`hRead`/`hE`・`hP`・`DesignTransport`・`EntryWitness` は前提に無いことを検査。
- `FGCIRCUIT9 AXIOMS`: 12 名、標準 axiom のみ。
- `FGCIRCUIT9 SNAPSHOT9`: 上の 15.1（1 環境の値）。`machine_closes` が root に**無い**ことも検査（生成されたら更新が必要）。

### 15.5 残り

`hcd`（`CD` の規則）、`hsrc`（`ExtStage` 帰納）、`htop`（machine 経路 `TopShips`、子の package/`ChildShips`/`ResetNk`、root の closing の供給）、`hnoraw`（run から「top に戻らない」を出す。全体の非巡回性は十分条件の一候補で、必須とは言わない）、`hreadH`/`hreadT` の `ReaderAt env₀` + `ContainsAt` への還元（S1i の root と同様）、S1i までの `HeadIO`・`reader`/`gates` の kernel 化。

4 root の final10 の仮説: `Laws L`・`hstart`（A.P-02）、`hr`（A.P-04）、`hhead : HeadAt`（C.EN-4: `coreHead` の 2件のIO動作の義務。`CellPrem` + `HeadIO` から）、`hcell : ReadWorld cref`（CellPrem）、`hchk : CheckedStart`（`root` = 型の文、`gates`/`reader` = 1 環境の評価、`link` = DG-ENV C0）、arbiter は `hB0`/`hcont`。
次: (1) `HeadIO`（2件のIO動作の義務）。(2) `reader`/`gates` の評価を kernel の文に（`dataOfAt` の `partial` helper の外出し）。(3) 非 leaf: `NoRawBelow` を run から出す補題と `TopShips` の machine 経路（insts 付き）、`hsrc` の `ExtStage` 帰納。

## 16. S1l（Issue `sparkle-fg-circuit-pilot` の次の束）: S1i/S1j の記録訂正、counterLoop の CheckedStart を有限入力に接続、HeadIO の完全型

土台 `8b4c135b`（par/fgc-s1）。追加ファイル（既存の定理は書き換えていない。lakefile 登録は 1 回）: `Tools/ShippingFGCircuitS1lReader.lean`、`Tests/Gen5/FGCircuitPilotCheck10.lean`。既存ファイルの変更は記録訂正のみ（`Tests/Gen5/FGCircuitPilotCheck8.lean` の SNAPSHOT8b とラベル、`Tools/ShippingFGCircuitS1iChild.lean` の冒頭コメント、本書 §14）。sorry・axiom・native_decide・TRUSTED・新しい law はない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。非 leaf の root と §15 は触っていない（S1k）。

### 16.1 作業 A: 記録訂正

- **SNAPSHOT8b**（Check8）: コンパイルしたのは private な `synth_hftPcieOutByte` 自身ではなくプローブ `hftOutProbe`（`(hftPcieLoop ..).outByte`）で、`synthesizeCombinationalCore` と外側の `synthesizeCombinational` を**別々に 2 回**実行して比べている。「ONE compile」「本体 = synth_hftPcieOutByte の」「first disjunct」の断言は外した。`PostEntry` は `dropZeroWidth` **または** `mergeChecked` の選言で、どちらの枝が成り立ったかを計算してログに出すようにした（この build: 両方 true、つまり `mergeChecked` はこの run で恒等）。**同一 run の PostEntry の証拠とは数えない**（`b` と `raw` は別の run）。
- **`S1iChild` 冒頭**: 「evaluated instead of assumed」を、評価は MetaM での観測で仮説の kernel 供給ではない、に訂正。
- **Check8 の対照の呼び分け**: SIGNATURES の head/`ReadsAt`/`CheckedStart`/find の対照は**同じ run の終点 w'**（end-world 対照）。MDLBODY の (b)(c) は無関係な独立 world `u`（independent-u 対照）。二つは別物としてラベルを付けた（SIGNATURES の 66 件は end-world 対照を含み、MDLBODY の 3 件は別集計）。
- **§14 の語**: `HeadIO` は「2件のIO動作の義務」（profile ログは複数の IO 動作の合成）、「導けない」は「現時点で供給経路が見つかっていない」、`NoRawBelow` の非巡回性は十分条件の一候補、`designTransport_of_noRawBelow` は全 n を要求し深さ 1〜6 の snapshot は供給しない、`CheckedStart` の 1 binder への束ねは減算ではない、に直した。

### 16.2 作業 B: counterLoop の CheckedStart（gates / reader）を有限入力に接続

**完全な型（Check10 で独立に書いた文面と isDefEq）。**
- 一般（どの root でも）: `EntryOfDecl d ip ui se := entryConst true false [] (.defnInfo d) ip ui se`、`GatesOnDecl d ip ui se`（`certifiedShape?` と `mixedCertifiedShape? … ip` が none）、`ReaderOnDecl lvl d ip ui se dd`（`machineShape? … = some dd.shape ∧ dataOfAt lvl … = some dd`）。`checkedEnv_of_decl : RootInEnv env₀ X ty val d → GatesOnDecl d (instancePredicate env₀) (userInliner env₀) (structEnv env₀) → ReaderOnDecl lvl d … dd → CheckedEnv lvl env₀ X ty val dd`。つまり `CheckedEnv.gates`/`reader` は、**閉じた宣言 `d`（`RootInEnv`）と環境由来の 3 引数**についての文になった。
- counterLoop: 名前付き Prop 2 つ。
  - `CounterLoopExtern`（環境に依らない閉じた 3 事実）: `packTupleInputs counterLoopValue = counterLoopValue`、`rootFloat counterLoopValue = counterLoopValue`、`counterLoopValue.find? (isAppOfArity runCircuitH 8) = none`。
  - `CounterLoopEnvFacts env₀`: `∃ d, RootInEnv env₀ counterLoop counterLoopType counterLoopValue d ∧ machineShape? false [] (.defnInfo d) (structEnv env₀) = some counterLoop.machineData.shape`、`userInliner env₀ counterLoopValue = counterLoopValue`、`userInliner env₀ counterLoopType = counterLoopType`、`instancePredicate env₀ counterLoopValue = false`、`(structEnv env₀).proj Signal.loop = none`。
  - 加えて `hlvl : lvl counterLoop.machineData.shape.body = 1000000`（`ReaderAt` は `lvl` を量化する。これまでの snapshot の fuel の前提を明示した）。
- `counterLoop_checkedEnv_of_finite lvl env₀ hlvl hx hf : CheckedEnv lvl env₀ counterLoop counterLoopType counterLoopValue counterLoop.machineData`、`counterLoop_final11`（`counterLoop_final10` の `hchk : CheckedStart` を `hlvl hx hf hlink` に替えた形。仮説: `L lvl env₀ hstart hr hhead hcell hlvl hx hf hlink`）。

**kernel が評価したもの（証明済み、標準 axiom のみ）。**
- gates: `certifiedShape?` は閉じた宣言に対して kernel が評価（`counterLoop_gates`）。`mixedCertifiedShape?` は `instancePredicate` を**値の 1 点だけ**で引く（`unifiedInstanceRoot`/`hierInstRoot` が `isInst e`）ので、`ip counterLoopValue = false` があれば none。`entryConst` が宣言自身になること（`entryOfDecl_eq`: `userInliner` が値と型を固定すれば、`machineShape?` を評価せずに `inlinedConst` が宣言に戻る）。
- reader のデータ: `mixedGatePeel`、`machRoot`（`proj Signal.loop = none` のとき）、`srcDomOf`（`Expr.find?` の事実のとき）、`machDom?`、`machOuts?`、`dataOfCore`（fuel 1000000）を経て**構造全体** `counterLoop.machineData` まで kernel が評価（`counterLoop_dataOfAt`）。これは DG_DATAOF_FREEZE が「evidence-only」とした kernel instance の 1 件に当たる（ただし 4 つの閉じた事実と `proj` の 1 点を仮説に取った条件付き）。
- 問い合わせ先の調査: `mixedCertifiedShape?` が `ip` を引くのは値の 1 点のみ、`dataOfAt` が `structEnv` を引くのは `proj Signal.loop` のみ（MetaM で引数にログを付けて実行して確認。`machineShape?` は `prodMatch` 等を多数引くが、これは仮説側）。

**行 ID ごとの残り義務（供給していない。評価は Check10 SNAPSHOT10 で 1 環境について確認しただけ）。**

| 義務 | 内容 | FG 行 |
|---|---|---|
| `hx.pack` / `hx.rootFloat` | `partial` の `packTupleInputs` / `rootFloat`（extern の `liftLooseBVars` を呼ぶ）の値。kernel は評価できない | DG-DATAOF T-X、DG-COVER S-COV-FLOAT |
| `hx.find` | `Expr.find?` は `opaque` の extern。`runCircuitH` を含まない | 行 ID 未割当（T-X と同種の extern 振る舞い。新しい行が要るなら reviewer 判断） |
| `hf.root` の `machineShape?` | `partial` の機械リーダ（`machConv` 等）。kernel は評価できない | DG-COVER、C.RK-6、C.CV-4（h_A_P06 の shape 部分） |
| `hf.root` の `RootInEnv` | `env₀` の `X` が型・値の閉じた宣言 | C.EN-4 QuoteFact、DG-ENV |
| `hf.ui_val` / `ui_ty` | `userInliner env₀` が値・型を固定（`userInliner` は環境を展開する） | DG-ENV |
| `hf.ip_val` | `instancePredicate env₀`（`@[hardware_module]` 属性表）が値で false | DG-ENV |
| `hf.proj_loop` | `userProjection? env₀ Signal.loop = none` | DG-ENV |
| `hlvl` | `lvl` の fuel | DG-DATAOF（Q5） |
| `hlink` | `ReadsAt env₀ cref w` | DG-ENV C0 |
| 変更なし | `hstart`（A.P-02）、`hr`（A.P-04）、`hhead`（C.EN-4、§16.3）、`hcell`（C.EN-4 CellPrem） | |

**減ったもの / 減っていないもの。** `CheckedEnv.gates`（`entryGatesB env₀ X = true`）と `reader`（`ReaderAt`）という env₀ 全体への評価文が、閉じた宣言と 3 引数の 1 点ずつの事実（上表）に分かれ、gates と reader のデータ部分は kernel の計算になった。`machineShape?`・`pack`・`rootFloat`・`find?` は kernel で評価できない（現在の方式では未供給。不可能性は証明していない）。仮説の個数は増えた（1 つの `CheckedStart` が 9 つの個別事実になった。内訳は `hx` 3 + `hf` 5 + `hlvl` 1 で、`hlink` は別掲（9 に含めない）。`hf.root` 自身も存在証人と複数の事実を含む 1 件なので、9 は仮説の最小単位の数ではない）ので、台帳には数えない（FG -0 +0 / T1 -0 +0）。

### 16.3 作業 C: HeadIO の完全型と許容する実行範囲

**型（`Tools/ShippingFGCircuitS1iHead.lean` の定義そのまま）。**
```lean
structure HeadIO (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) : Prop where
  getEnv : EnvFrame (liftM (IO.getEnv "SPARKLE_PROFILE") : MetaM (Option String)) mctx mref cctx cref
  log : ∀ msg, EnvFrame (liftM (profLogIO true msg : IO Unit) : MetaM Unit) mctx mref cctx cref
-- EnvFrame x mctx mref cctx cref := ∀ w a w', RunsTo x mctx mref cctx cref w a w' → envAt cref w' = envAt cref w
```
2 件の IO 動作の義務: (1) `IO.getEnv "SPARKLE_PROFILE"`、(2) `profLogIO true msg`（`msg` は全ての文字列。複数の IO 動作の合成）。`profLogIO false msg = pure ()` は証明済み（`ef_prof_false`）。成功した run（`RunsTo` は `EST.Out.ok`）だけを問うので、IO 例外で終わる run は対象外。

**許容する実行範囲（この義務が許す IO 動作。これ以外を含む `coreHead` には使えない）。**
- `IO.getEnv "SPARKLE_PROFILE"`: プロセス環境変数 `SPARKLE_PROFILE` の**読み取りのみ**。他の環境変数の読み書き、`setenv` は含まない。
- `SPARKLE_PROFILE` が**未設定**のとき: ログ動作は `pure ()`（IO なし）。
- `SPARKLE_PROFILE` が**設定されている**とき（`profLogIO true msg`）: (a) `IO.eprintln msg`（stderr への書き込み）、(b) `Sparkle.Compiler.flushStderr`（`(← IO.getStderr).flush`）、(c) `IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append`（固定パスのファイルを追記で開く）、(d) `h.putStrLn msg`、(e) `h.flush`。他のファイル・ネットワーク・サブプロセスは含まない。
- どの動作も `ST.Ref`（`cref`、`mref`）に触れず、`Core.State` の `env` を変えない、が義務の内容。

**必要になる新しい law の凍結ドラフト（【未承認・凍結前のドラフト】。供給済みとして使っていない。コードにも入れていない）。**
```
IOHeadFrame (draft, UNAPPROVED, not used):
  IOHeadAct : (α : Type) → IO α → Prop   -- 閉じた inductive。生成規則は次の 3 つの原始 + 閉包のみ
    | getEnvProfile : IOHeadAct _ (IO.getEnv "SPARKLE_PROFILE")
    | profLog       : IOHeadAct _ (profLogIO true msg)   -- ∀ msg
    | bind / pure   : 上記の bind と pure で閉じる（制御は ite のみ）
  law IOHeadFrame (mctx mref cctx cref) :
    ∀ α (x : IO α), IOHeadAct α x → EnvFrame (liftM x : MetaM α) mctx mref cctx cref
```
意味: 「列挙した IO 動作を `liftM` した MetaM は `envAt cref` を変えない」。実ランタイムでは `cref` は `ST.Ref` のセルで、列挙した動作は stderr・固定パスのファイル・環境変数の読み取りしか行わず、そのセルを参照しない、という実行モデルの主張（Lean の `IO.getEnv`/`IO.FS.Handle` は外部関数で、kernel の中身が無い）。既存の C.EN-4 `CellPrem`/`QuietStrength`/`Laws` に吸収されるか、新しい行になるかは reviewer の判断。**これが承認されるまで `HeadIO` は仮説のまま**で、`hhead`（`HeadAt`）は引き続き final の仮説である。

### 16.4 Check の出力

`kjob lake build Tests.Gen5.FGCircuitPilotCheck10`（911 jobs、exit 0。Check8 も同じ build で再実行）:
- `FGCIRCUIT10 SIGNATURES`: `checkedEnv_of_decl`、`CounterLoopExtern.mk`、`CounterLoopEnvFacts.mk`、`counterLoop_dataOfAt`、`counterLoop_gates`、`counterLoop_checkedEnv_of_finite`、`counterLoop_final11` の完全型を独立に書いて `isDefEq` で照合。**27 mutant 棄却**（ゲート/reader/lvl/extern/環境事実の欠落、別の値・型・データ・post root、`ip` の極性、`proj` を引く名前、`runCircuitH` の arity、fuel、end-world 対照＝同じ run の終点 w' での head 開始・link・結論の環境）。
- `FGCIRCUIT10 HYPS`/`REMAINING`: `counterLoop_final11` の仮説名と型。`hchk : CheckedStart`・`hgatesB`・`hquote`・`hreader` は仮説に無い。
- `FGCIRCUIT10 AXIOMS`: 13 名、標準 axiom のみ。
- `FGCIRCUIT10 SNAPSHOT10a/b/c`: 1 環境の評価（仮説の供給ではない）。(a) `CounterLoopExtern` と `CounterLoopEnvFacts` の各事実、`machineShape?` が読んだ `dataOfAt` の全体が `counterLoop.machineData`。(b) `ip` を値以外で全て true、`proj`/`fields` を `Signal.loop` 以外で何か返すように替えてもゲートとデータは不変（問い合わせ先の確認で、独立性の証明ではない）。(c) 別 root の値では別のデータ（または none）、`instancePredicate` は `httpGetByte` で true（`ip_val = false` は空虚ではない）。
- Check8（再実行）: 66 mutant（SIGNATURES）、MDLBODY 3 mutant、AXIOMS 27 名、SNAPSHOT8b は上記の訂正後の文言。

### 16.5 次

(1) `hx` の 3 事実と `machineShape?` の kernel 供給（`partial` 本体の外出しか、対応する law の凍結）。(2) `CounterLoopEnvFacts` の環境側 4 点（`ui`/`ip`/`proj`/`RootInEnv`）を `ReadsAt`＋属性表の文に落とす。(3) `HeadIO` の凍結ドラフト（§16.3）の reviewer 判断。(4) 他の 3 root（shift4Loop/counterEnableLoop/arbiterSignal）へ `X_final11` を持ち上げる（counterLoop と同じ手順。問い合わせ先は root ごとに調べ直す）。

## 17. S1m（Issue `sparkle-fg-circuit-pilot` の次の束）: `CD` の設計穴 — 利用者定義の展開と構造体射影の規則（**FREEZE DRAFT: reviewer 承認待ち**）

土台 `07752341`（par/fgc-s1）。注: 土台 07752341 には §16 が無かった（S1l は別に進め、後で merge した）。追加ファイル（既存は書き換えていない。lakefile 登録は各 lib 1 回）: `Tools/ShippingFGCircuitS1mCD.lean`、`Tests/Gen5/FGCircuitPilotCheck11.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない（`FGCIRCUIT11 AXIOMS`: 16 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。Issue の状態は変えていない。**この規則集合は FREEZE DRAFT であり、reviewer が承認するまで `HftObCD` の型にも final 定理にも使わない**（既存の `CD`・`HftObCD` は変えていない）。

### 17.1 問題と設計方針

`hcd : HftObCD = CD [] hftRootValue (MonoTy shHft) synth_hftPcieOutByte` が供給できない理由は、`CD` に (1) 利用者定義定数（`hftPcieLoop`）の適用の規則も、(2) 構造体射影（`HFTPcieOut.outByte`）の規則も**無い**ことである。これは証明の埋め残しではなく規則集合の設計穴（reviewer の判断）。そこで `CD` を**書き換えず**、新しい関係 `CDX` を足した。

- `CDX env ρ e α v` / `TDX env ρ e T` は**固定の `env : Environment`** をパラメータに持つ。実体は 1 つの帰納族 `DX env : Val → Expr → Res → Prop`（`Res.ty T` / `Res.val α v`）で、`TDX`/`CDX` はその `abbrev`。1 つの族にしたのは、関数性の証明を**導出に関する `induction`** にするため（§17.4）。
- `CD`/`TD` の 18+5 規則は**同じ型のまま** `DX` に入っている（`env` を通すだけ。Check11 が構造比較）。埋め込み `cdx_of_cd : CD ρ e α v → CDX env ρ e α v`、`tdx_of_td` を証明した（任意の `env`）。`circCV_to_X : CircCV env X α v → CircCVX env env X α v`。
- 表示対象は従来どおり **Lean の値そのもの**（各規則の値は同じ Lean 定数で組む）。新規則は値を `v` のまま次の導出へ渡す（`unf`: 結論の `v` は前提の `v`）。**新規則が元の Lean 式の意味を保つこと自体は S1m では証明していない**（下 17.2 の「対応する Lean の操作」は監査対象。S1p の訂正は §17.8）。

### 17.2 新しい 5 規則の完全な型（`Tools/ShippingFGCircuitS1mCD.lean`、`DX` のコンストラクタ）

記法: `CDX env ρ e α v` = `DX env ρ e (Res.val α v)`。以下の関数は全て Lean で書いた**カーネルが評価できる**構造再帰（`Expr.instantiate` は opaque extern なので使えない。自前の `instE`/`betaApp`/`instLE`。Check11 OPS が Lean の `instantiate1`/`Expr.beta`/`instantiateLevelParams` と一致することを実環境の定義 21 件で比較した。**これは監査であり、規則の意味保存の証明ではない**: §17.8）。

| 規則 | 型（前提 → 結論） | 対応する Lean の操作（監査対象。意味保存は今回証明していない: §17.8） |
|---|---|---|
| `unf` | `headStop e = false` → `unfoldAt env e = some e'` → `CDX env ρ e' α v` → `CDX env ρ e α v` | delta + beta。`unfoldAt env e`: `e` の頭が定数 `c`、`env.find? c = some (.defnInfo d)`、`d.levelParams.length = ls.length` のとき `betaApp (instLE d.levelParams ls d.value) (args)`。`headStop e` は頭が `CD` の primitive（`Signal.pure/register/mux/loop`、`HAdd/HAnd/HOr/Complement`、`Signal.beq`、`BitVec.ofNat` 他 14 頭）か `bvAbbrevRow` の行のときだけ true（primitive の規則が意味であり、展開しない） |
| `beta` | `headRedex env e = some e'` → `CDX env ρ e' α v` → `CDX env ρ e α v` | 頭がラムダ/`let`/射影の適用（`(fun x => b) a …`、`(let x := v; b) a …`、`(p.i) a …` で頭が `whStep` で進む）。`unf` が引数を代入して作る redex を縮める。beta/zeta/射影の頭の一歩 |
| `zeta` | `e = .letE n A v b nd` → `coreHead A = false` → `CDX env ρ (instE b v 0) α r` → `CDX env ρ e α r` | `let` の zeta（代入）。`coreHead A = false` は型の頭が `Nat/Bool/DomainConfig/BitVec/Signal` でないとき。この型は旧 `letE` 規則の `TD` が扱えないので重ならない（`coreHead_td : TDX … A T → coreHead A = true`） |
| `projStep` | `e = .proj S i x` → `whStep env x = some x'` → `CDX env ρ (.proj S i x') α v` → `CDX env ρ e α v` | 構造体引数の弱頭 1 歩（zeta、beta、頭定数の delta、射影の下の 1 歩、射影の iota） |
| `projCtor` | `e = .proj S i x` → `appFn x = .const ctor ls` → `env.find? ctor = some (.ctorInfo cv)` → `cv.induct = S` → `(appArgs x).length = cv.numParams + cv.numFields` → `(appArgs x)[cv.numParams + i]? = some fld` → `CDX env ρ fld α v` → `CDX env ρ e α v` | 構造体のコンストラクタ適用への射影（iota）。構造体の情報は `env` の `ctorInfo` から読む |

構造体射影 `HFTPcieOut.outByte dom x` は射影関数（`defnInfo`、値は `fun dom self => self.1` の `Expr.proj`）なので、`unf` で `Expr.proj` になり、`projStep`/`projCtor` が扱う。**型の付いた Lean 構造体値**（構造体型の値そのものを `ρ` に束縛する）は今回の規則に入れていない（構造体ごとに Lean の型と射影関数の行が要り、境界の行が増えるため。必要なら次の束で reviewer に諮る）。

**停止性・整礎性**: 導出は有限の木（帰納 `Prop`）であり、`unf` を使った導出が存在するとは**その導出が有限に閉じる**ことと同じ。再帰・相互再帰の定義は `unf` を繰り返すだけでは導出が閉じない（`brecOn`/`rec` に規則が無い）。**今回の走査はそこで停止する。導出は未供給**（走査は導出の不存在証明ではない）。燃料もサイズ尺度も使わない（`CD` の関数性は `sizeOf e` による整礎再帰だったが、`unf` は式を大きくするので使えない。S1m の関数性は導出の `induction`）。

### 17.3 環境との結び付き（ReadsAt / CheckedStart 流）

`CDX` の `env` は固定のパラメータである。run の環境との結び付きは**仮定**として足す: 具体的な導出は有限表 `Δ : Name → Option DefRow`（定数名 → 宇宙パラメータと値の `Expr`）と `Γ : Name → Option CtorRow` を使い、`EnvDefs env Δ`（`Δ c = some r` なら `env.find? c = some (.defnInfo d)`、`d.levelParams = r.lps`、`d.value = r.value`）と `EnvCtors env Γ` を**仮定**する。補題 `cdx_unf_tbl`（`unf` の表版）と `cdx_projCtor_tbl`（`projCtor` の表版）が、表の行から規則の前提を作る。`env := envAt cref w`（`CheckedStart` と同じ world）として、`EnvDefs`/`EnvCtors` は `hchk` 流の「表と環境の一致」で、**meta 検査（Check の SNAPSHOT: 表と環境の `ConstantInfo` の一致）**であり kernel は環境を見ない。これは `RootInEnv` と同じ種類の境界だが、**`EnvDefs`/`EnvCtors` は実 run 環境について追加の未供給内容**であり、meta 照合で支払い済みとは扱わない（S1p 訂正: §17.8）。

### 17.4 関数性（証明した）

`dx_fun : DX env ρ e r → DX env ρ e r' → r.kind = r'.kind → r = r'`（導出に関する `induction`。`kind` は型/値の別）。系: `cdx_fun : CDX env ρ e α v → CDX env ρ e α' v' → α = α' ∧ HEq v v'`、`tdx_fun`、`cdx_eq`（同じ型なら値が等しい）、`circCVX_functional : ConstValueFunctional (CircCVX env)`。規則の衝突は頭の定数・構造の違いで反駁する（`unf` と primitive は `headStop`、`unf` と `beta` は `unfoldAt_none_of_beta`、`projStep` と `projCtor` は `whStep_ctor`、`zeta` と `letE` は `coreHead_td`）。**関数性は仮定を置かずに成り立つ**。ただし `cdx_fun` は**新しい関係 `CDX` の一意性**であり、元の Lean 式との一致ではない（§17.8）（`EnvDefs` 等を使わない。`unfoldAt env e` は `env` と `e` の関数）。`ty` と `val` の導出が同じ式にあり得るので、statement は同じ kind に限る（`env` が任意なので式の頭が型であり値でもあり得る）。

### 17.5 hftPcie のどの部分項が何を要するか（Check11 SNAPSHOT11、1 環境の値）

`Check11` の recognizer は規則の関数（`unfoldAt`/`headRedex`/`whStep`/`instE`）をそのまま使い、`root` の値を走査して**規則が尽きる所**を出力する（証明ではなく走査）。観測（`hftRootValue` から）:

- 5 つのラムダの本体 `HFTPcieOut.outByte dom (hftPcieLoop dom rx v s d c)`: `unf`（射影関数 `outByte` → `Expr.proj`）→ `projStep`（`hftPcieLoop` の delta）→ `zeta` 2 回（`let ep := mmioEndpoint …; let emit := httpGetEmitter ep.writePulse`。型は構造体なので `zeta`）→ `projCtor`（`HFTPcieOut.mk` 適用、`outByte` の項）→ `HttpEmitOut.byte dom (httpGetEmitter …)` → `unf`/`projStep`（`httpGetEmitter` → `burstEmit` → `runCircuitH …`）。ここまでは新規則で**進む**（走査が 454 節点、定義 22 個を展開: `Prod.fst`、`eqK`、`httpGetByte`、バイト定数 `cG…`、`runCircuitH`、`burstEmit`）。
- **規則が尽きる所**（`MISSING`、走査の stuck。S1p 時点の更新は §20.4）: `Expr.proj Prod 0 (… (PProd#0 (List.rec …) …))` ×17。つまり `circuit do` の状態を持つ `runCircuitH` の中の **`List.rec`（再帰子。`List.brecOn` による構造再帰）の適用**。`CDX` に再帰子の規則（コンストラクタ引数の iota）が無い。これを足すか（`List` の具体値が必要）、`circuit do` のモナド（`Circuit` 型、`Signal.reg` と `<~`）を別の規則にするかが次の設計問題。
- `tdFail`（`TD` に無い束縛/let の型）: なし。

したがって **`hcd` は今回の `CDX` でも導出できない**（供給しない）。`HftObCD` は未供給のまま。次に要るのは (a) `List.rec` 等の再帰子 iota（`env` の `recInfo` の規則を読む）と、(b) 構造体値の型付き規則（必要なら）。いずれも reviewer の判断を仰ぐ（本書は設計の草案）。

### 17.6 範囲外（明記）

- **回路の核のみ**。`Dyn` への拡張はしない。利用者定義の型（型 abbrev の展開）は `TDX` に入れていない。
- 再帰子（`rec`/`casesOn`/`brecOn`/`WellFounded.fix`）、`match`、型クラス引数の解決、`Id.run`/モナドの束縛は規則に無い。
- 構造体値を `ρ` に束縛する型付き規則、`HftObCD` の型の差し替え、`hcd` の供給は今回しない。
- `EnvDefs`/`EnvCtors` と実環境の一致は meta 検査であり kernel の定理ではない。

### 17.7 Check11 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck11`、911 jobs、exit 0）

- `FGCIRCUIT11 SIGNATURES`: 新 5 規則（`DX.unf/beta/zeta/projStep/projCtor`）、埋め込み `cdx_of_cd`/`tdx_of_td`、関数性 `cdx_fun`/`tdx_fun` の完全な型を独立に書いた文面と `isDefEq`（default 透過度）で照合。旧 23 規則（`CD` 18 + `TD` 5）が `env` を通しただけで同一であることを構造比較（`CD` の `sigMux` を `sigPure` と見る control は棄却）。**23 mutant 棄却**: `unf`（stop 条件なし、stop の反転、`ρ` の初期化、結論が `e'`、unfold の向きの入れ替え）、`beta`（`unfoldAt` を使う、結論が `e'`）、`zeta`（core 条件なし、代入なし、条件が true）、`projStep`（`unfold` のみ、`proj` を捨てる）、`projCtor`（inductive の一致なし、引数個数なし、field 添字が `i` のみ、`numParams` のみ）、埋め込み（逆向き、`ρ` の初期化）、関数性（別の env、別の `ρ`、`HEq` なし）、`tdx_fun`（別の env）。
- `FGCIRCUIT11 OPS`: `betaApp`/`instE`/`instLE` が Lean の `Expr.beta`/`instantiate1`/`instantiateLevelParams` と、recognizer が展開した実環境の定義 21 個（引数は loose bvar、宇宙は sample）で一致。誤った代入を検出する control あり。
- `FGCIRCUIT11 AXIOMS`: 16 名、標準 axiom のみ。使える導出の例 `ex_projCtor`（`(3,4).1 ⇓ 3`）、`ex_unf`（`mini := Signal.pure 5` の展開）、`ex_zeta`（構造体型の `let`）が通る。
- `FGCIRCUIT11 SNAPSHOT11`/`MISSING`: 17.5 の走査結果。

### 17.8 訂正（S1p、reviewer 裁定 M2）と意味保存の経路

S1m の以下の文言は今回の証明結果ではなかったので撤回・言い換える。

1. 「健全性（定義的等式）」「各規則は定義的等式」「新規則は値を変えない」: **証明していない**。`Expr` に意味論が無いので、`unfoldAt`/`betaApp`/`instE`/`whStep` が元の Lean 項を保つことは Lean の定理として述べられていない。Check11 OPS の 21 件（`instE`/`instLE`/`betaApp` と Lean の `instantiate1`/`instantiateLevelParams`/`Expr.beta` の比較）は**監査**である。
2. `cdx_fun`/`dx_fun` は**新しい関係 `CDX` の関数性（導出の一意性）**であって、導出の値が元の Lean 項に一致することではない。
3. `projCtor` は**生の `Expr` に対する規則**である。`ctorInfo` の読み取りは、Lean の構造体射影の型の正しさ（その `Expr.proj S i x` が型付けされていること）を保証しない。同じ境界である。
4. `EnvDefs`/`EnvCtors`（実 run 環境の表）は**追加の未供給内容**である。既存の境界（`RootInEnv` 等）と同種だが、meta 照合（Check の比較）で支払い済みとは扱わない。
5. 再帰定義について「導出が存在しない」と書いた箇所（§17.2 停止性、§17.5）は「今回の走査はここで停止する。導出は未供給」に直した。走査は不存在の証明ではない。

**意味保存の経路（2 つ。どちらか）**:
- (a) 型の正しい入力・環境に対して縮約（delta/beta/zeta/射影/iota）が意味を保つこと自体を証明する。`Expr` の型付き意味論が要り、今回も未実装。
- (b) **対象 root で等式証明をカーネルに渡す**: 導出 `h : CDX env [] e α v` を組むとき `v` は規則の値から**構成される** Lean の値であり、結論の型 `HftObCD`（`v := synth_hftPcieOutByte`、元の Lean 定数）は `v` と構成された値が**カーネルの定義的等式**で一致する場合にのみ型検査を通る。つまり (b) は元の Lean 項と展開後の項の等式証明をカーネルに検査させる経路で、**規則の健全性を一般には要らない**（その root について導出が受理された時点で等式が検査済み）。ただし受理される導出が未供給の間、(b) も供給されていない。
S1p の再帰子単位は (b) で扱う（§20.3）。

## 18. S1n（Issue `sparkle-fg-circuit-pilot` の次の束）: 他の 3 leaf root への `X_final11` の持ち上げ

土台 `a24f49c4`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 lib 1 回）: `Tools/ShippingFGCircuitS1nRoots.lean`、`Tests/Gen5/FGCircuitPilotCheck12.lean`。sorry・axiom・native_decide・TRUSTED・新しい law はない。S1m の領域（`Tools/ShippingFGCircuitS1mCD.lean`、§17）は触っていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。

### 18.1 証明したもの

`shift4Loop_final11`、`counterEnableLoop_final11`、`arbiterSignal_final11`（`counterLoop_final11` と同じ形。仮説: `L lvl env₀ hstart hr hhead hcell hlvl hx hf hlink`、arbiter は更に `hB0 hcont`）。それぞれ `X_final10` の `hchk : CheckedStart` を `hlvl hx hf hlink` に替えたもの。途中の定理: `X_gates`（arbiter は `_orig`/`_inl` の 2 件）、`X_srcDomOf`、`X_dataOfCore`、`X_dataOfAt`、`X_checkedEnv_of_finite`。共通: `entryOfDecl_inl`（入口定数 = 値を `Vi`、型を `T` に書き換えた宣言）、`checkedEnv_of_inl`、`dataOfAt_of_pieces`、`machRoot_of_head`。標準 axiom のみ（`#print axioms`、Check12 の AXIOMS）。

**kernel が評価したもの（`with_unfolding_all rfl`、最初の試行で全部通った）。** 3 root とも `certifiedShape?`／`mixedCertifiedShape?`（閉じた宣言、gate binder の剥離 `mixedGatePeel` を含む）、`machRoot`／`srcDomOf`、`dataOfFront`、`dataOfCore`（fuel 1000000）を経て**構造全体** `X.machineData` まで。arbiter の `dataOfCore`（binder 16、スロット含む）も通った。評価が止まった部分は**なかった**ので、「止まった部分」の記録はない。残るのは下の名前付き仮説だけ（kernel が評価できない `partial`/extern、環境への問い合わせ）。

### 18.2 counterLoop との違い（root ごとに問い合わせ先を調べ直した結果）

問い合わせ先は `dbgTrace` 付きの述語・`StructEnv` を MetaM で走らせて調べた（Check には入れていない調査。Check12 は「その点以外では不変」を確認する）。
- **`instancePredicate`**: counterLoop は値（binder なし）だが、他 3 root の値は `fun` なので、問い合わせ点は `mixedGatePeel` で剥いだ**本体** `peeledBody V`。`rootFloat`／`Expr.find?` の引数も同じ本体。`packTupleInputs` は入口の値。
- **`structEnv.proj`**: shift4Loop は `Signal.register`（本体の先頭定数）、counterEnableLoop と arbiterSignal は `Signal.loop`。`dataOfAt` が `proj` を引くのはこの 1 名だけ（`fields`／`inst`／`natOf` は `dataOfAt` では引かれない。`prodMatch` 等は `machineShape?`＝仮説側）。
- **`userInliner`**: shift4Loop／counterEnableLoop は値と型を固定する（counterLoop と同じ）。**arbiterSignal は値を変える**（private の状態定数 `stIdle` 等がリテラルになる）ので入口定数は**インライン後の宣言** `{d with value := Vi, type := T}`。`entryConst` は「元の宣言のゲートが none ∧ インライン後で `machineShape?` が some」のとき `inlinedConst` を返す（`entryOfDecl_inl`）。そのため arbiter はゲートを元の値とインライン後の値の 2 つで評価し、`instancePredicate` も 2 点（`peeledBody V`、`peeledBody Vi`）で引かれる。
- `Vi` の閉じた項: `arbiterInlinedValue`。コマンド `quote_inlined%` が**この build の `userInliner env` の出力**を `Expr` の項として定義する（`quote_value%` と同じ引用）。つまり**1 環境のスナップショット**で、`ui_val : userInliner env₀ arbiterValue = arbiterInlinedValue` が名前付き仮説。Check12 が「この build で等しい」「インライナーは arbiter の値を変える（ui_val は自明でない）」を確認する。

### 18.3 名前付き仮説（root ごと）

共通の 2 つの構造に整理した（因子化は下の 18.4）。
- `RootExtern Vi : Prop`: `pack : packTupleInputs Vi = Vi`、`rootFloat : rootFloat (peeledBody Vi) = peeledBody Vi`、`find : (peeledBody Vi).find? (isAppOfArity runCircuitH 8) = none`。（DG-DATAOF T-X、DG-COVER S-COV-FLOAT、find は行 ID 未割当で S1l と同じ扱い。`partial`／`opaque` extern でkernel は評価できない。不可能性は主張しない。）
- `RootEnvFacts env₀ X T V Vi dd projName : Prop`: `root : ∃ d, RootInEnv env₀ X T V d ∧ machineShape? false [] (.defnInfo {d with value := Vi, type := T}) (structEnv env₀) = some dd.shape`（DG-COVER、C.RK-6、C.CV-4、C.EN-4 QuoteFact。`machineShape?` は `partial` の機械リーダ）、`ui_val : userInliner env₀ V = Vi`、`ui_ty : userInliner env₀ T = T`、`ip_val : instancePredicate env₀ (peeledBody V) = false`、`ip_inl : instancePredicate env₀ (peeledBody Vi) = false`（DG-ENV）、`proj : (structEnv env₀).proj projName = none`（DG-ENV）。

| root | `hx` | `hf`（`V` → `Vi`、`projName`） | 追加 |
|---|---|---|---|
| shift4Loop | `RootExtern shift4LoopValue` | `RootEnvFacts env₀ shift4Loop shift4LoopType shift4LoopValue shift4LoopValue shift4Loop.machineData Signal.register` | — |
| counterEnableLoop | `RootExtern counterEnableLoopValue` | `… counterEnableLoopType counterEnableLoopValue counterEnableLoopValue counterEnableLoop.machineData Signal.loop` | — |
| arbiterSignal | `RootExtern arbiterInlinedValue` | `… arbiterType arbiterValue arbiterInlinedValue arbiterSignal.machineData Signal.loop` | `hB0`（`BoundaryRowsInEnv env₀`）、`hcont`（`ContainsAt env₀ cref w boundaryNames`）— `ReadsAt` は存在を運ばない |

共通: `hlvl : lvl X.machineData.shape.body = 1000000`（DG-DATAOF Q5）、`hlink : ReadsAt env₀ cref w`（DG-ENV C0）、`hstart`（A.P-02）、`hr`（A.P-04）、`hhead`（C.EN-4、`HeadIO` は §16.3 の凍結ドラフトのまま）、`hcell`（CellPrem）。shift4Loop／counterEnableLoop では `Vi = V` なので `ip_val` と `ip_inl` は同じ文の重複（弱めてはいない）。

### 18.4 共通構造への因子化

4 root の構造は同じ形（外部ヘルパ 3 事実、環境の 5 点＋root）なので、3 root 分を `RootExtern`／`RootEnvFacts` に因子化した。フィールドは**どれも落としていない**: counterLoop の `CounterLoopEnvFacts` の 5 点（root、`ui_val`、`ui_ty`、`ip_val`、`proj_loop`）に対応する全フィールドを持ち、インライナーが値を変える root のために `ip_inl` と `machineShape?` の対象宣言（インライン後）を追加しただけ（`Vi = V` のとき追加分は元と同じ文）。`counterLoop_final11` と S1l のファイルは書き換えていない（counterLoop 自身の構造は S1l のまま）。arbiter の `hx` は `arbiterInlinedValue`（入口の値）についての文で、元の値についての文ではない（Check12 の `MutCFAExternOnValue` で棄却）。

### 18.5 Check12 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck12`、913 jobs、exit 0、error 0）

- `FGCIRCUIT12 SIGNATURES`: 17 定理（`RootExtern.mk`、`RootEnvFacts.mk`、`entryOfDecl_inl`、`checkedEnv_of_inl`、ゲート 4 件、`dataOfAt` 3 件、`checkedEnv_of_finite` 3 件、3 つの `X_final11`）の完全型を独立に書いて `isDefEq`（default）で照合。**117 mutant 棄却**（検査ごとに数える）: `rootFloat`／`find?`／`packTupleInputs` の引数（本体でなく値）、`runCircuitH` の arity、`instancePredicate` を値で引いたもの（本体でない）、極性、`machineShape?` の対象（インライン前）、インライナーの引数、`proj` を引く名前、fuel、別 root の data／値／型／extern の値／head の root／post の root、arbiter のインライン前の値、fuel・extern・環境事実・`hB0`・`hcont` の欠落、end-world 対照（同じ run の終点 w' での head 開始・link・結論の環境）、他 root の最終定理。
- `FGCIRCUIT12 HYPS`/`REMAINING`: 3 つの final の仮説名と型。`hchk`・`hquiet`・`GetEnvFrame`・`hdRun`・`hsrc`・`hcd`・`htop`・`hnoraw` は仮説に無い。構造のフィールド名も検査。
- `FGCIRCUIT12 AXIOMS`: 24 名（`arbiterInlinedValue` を含む）、標準 axiom のみ。
- `FGCIRCUIT12 SNAPSHOT12a/b/c`: 1 環境の評価（仮説の供給ではない）。(a) 3 root で `RootExtern` の 3 事実、`RootEnvFacts` の各点、`machineShape?` が読んだ `dataOfAt` の全体が `X.machineData`、`EntryOfDecl` がインライン後の宣言。(b) `ip` を 2 つの本体以外で全て true、`proj`／`fields` を 1 名以外で `some`、インライナーを値・型以外で任意の項にしても、ゲート・入口定数・データは不変（問い合わせ先の確認で、独立性の証明ではない。問い合わせ点が本体であることはロギング調査で見つけたもので Check の検査ではない。値だけで true にしてもゲートは不変）。(c) `arbiterInlinedValue = userInliner arbiterValue`、インライナーが arbiter の値を変え shift4Loop／counterEnableLoop を固定すること、shift4Loop の shape に arbiter の値（gate binder 3）を渡すと none か別データ、`httpGetByte` で述語が true。**注（訂正すべき期待）**: データは `machineShape?` が読んだ shape から出るので、gate binder 数とドメインが同じ別 root の値（counterEnableLoop を shift4Loop の shape に）は同じデータを返す。値が効くのは binder 数とドメインを通してで、「別の値は別のデータ」という対照は binder 数が違う root に限る。

### 18.6 残り

(1) `hx` の 3 事実と `machineShape?` の kernel 供給（`partial` 本体の外出しか対応する law の凍結）。(2) `RootEnvFacts` の環境側（`ui`／`ip`／`proj`／`RootInEnv`）を `ReadsAt`＋属性表の文に落とす。arbiter は `arbiterInlinedValue` が 1 環境のスナップショットなので、インライナーの出力の導出（`userInliner` の kernel 評価か名前付き law）も要る。(3) `HeadIO`（§16.3）の reviewer 判断。(4) 非 leaf（§15 の `hcd`／`hsrc`／`htop`／`hnoraw`、S1m の `hcd` 規則）。

## 19. S1o（Issue `sparkle-fg-circuit-pilot` の次の束）: HeadIO の再設計（profile 無効の run 形を先に）

土台 `a24f49c4`（par/fgc-s1）。追加ファイル: `Tools/ShippingFGCircuitS1oHead.lean`、`Tests/Gen5/FGCircuitPilotCheck13.lean`（lakefile 登録は各 1 回）。既存の定理は書き換えていない（記録訂正のみ: S1iHead 冒頭コメント、S1iChild 冒頭コメント、§16.2 の 9 の内訳）。sorry・axiom・native_decide・TRUSTED・新しい law はない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**。Issue の状態は変えていない。S1m/S1n のファイルには触れていない。

### 19.1 記録訂正

- S1iHead 冒頭: 旧「not derivable」「two opaque primitives」を §14 と同期（「供給経路が見つかっていない。導出不能の証明はない」「profile ログは複数の IO 動作の合成」）。∀world のログ義務を法則として採らない旨（所見C）を追記。
- S1iChild 冒頭: 「compile of the probe の one run」を、`synthesizeCombinationalCore` と外側の `synthesizeCombinational` の**別々の 2 回の実行**の観測に同期。
- §16.2 の「1 つの `CheckedStart` が 9 つの個別事実」は `hx` 3 + `hf` 5 + `hlvl` 1。`hlink` は別掲で 9 に含めない。`hf.root` 自身も存在証人と複数の事実を含む 1 件なので、9 は仮説の最小単位の数ではない。

### 19.2 (a) `coreHead` が profile を決める箇所と、狭めた run 形

`coreHead X` の**最初の動作**が `profile := (← IO.getEnv "SPARKLE_PROFILE").isSome`。ログ動作 `logProf` は `profile` が真のときだけ `IO.eprintln`、`flushStderr`、`IO.FS.Handle.mk`、`putStrLn`、`flush` を行う。`profile` は後で `CoreSaved.profile` にも入る（環境には触れない）。

評価した 2 案:
1. **run 局所の前提（採用）**: 開始 world `w` で `IO.getEnv "SPARKLE_PROFILE"` を走らせた結果が `none` で、環境 `envAt cref` を保つ、という run の前提。実環境変数が未設定という Meta の観測は**供給に使わない**（名前付き仮説のまま）。
2. **コンパイル時/オプションの切替**（提案のみ。Elab は変更していない）: `SPARKLE_PROFILE` の読み取りとログ枝を `register_option`/`Options` の値に移す（`Core.Context.options` から読む）と、`coreHead` から `IO.getEnv` と `logProf` が消え、`profile` は純粋な値になる。baseline 保存の論拠: 既定値 `false` では `profile = false` の枝が今と同一（出力 IR・`CoreSaved` の `profile` 欄は同じ）で、IP の出力・成功の run は変わらない。ただし `SPARKLE_PROFILE` を使う既存の運用（環境変数でログを出す）は、オプション指定に変わる（または変数→オプションの橋渡しが別に要る）ので、利用者に見える変更になる。これは compiler の変更なので S1o では実装しない。reviewer 判断。
   **訂正（S1q, §21）**: 上の「`coreHead` から `IO.getEnv` と `logProf` が消え」は誤り。`Options` に移しても `profile` が真の枝（`IO.eprintln`/`flushStderr`/`Handle.mk`/`putStrLn`/`flush`）は `coreHead` に残る。消えるのは `IO.getEnv` だけで、ログ枝は `profile = false` を**純粋な設定/引数で固定**したときにだけ消える。§21 は後者を実装する。

**最小の getEnvProfile frame の正確な型**（`Tools/ShippingFGCircuitS1oHead.lean`）:
```lean
abbrev profileAct : MetaM (Option String) := liftM (IO.getEnv "SPARKLE_PROFILE")
structure GetEnvProfileAt (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context)
    (cref : ST.Ref IO.RealWorld Core.State) (w : Void IO.RealWorld) : Prop where
  unset : ∀ (o : Option String) (w1 : Void IO.RealWorld), RunsTo profileAct mctx mref cctx cref w o w1 → o = none
  env   : ∀ (o : Option String) (w1 : Void IO.RealWorld), RunsTo profileAct mctx mref cctx cref w o w1 → envAt cref w1 = envAt cref w
```
全 world の `EnvFrame` ではなく run の開始 world 1 点で、結果を `none` に限る。

### 19.3 (b) 既存の EnvFrame 補題だけでの定理

- `headAt_of_profileOff (X) (hcell : CellPrem MkRefd mref cref) (hg : GetEnvProfileAt mctx mref cctx cref w) : HeadAt X mctx mref cctx cref w`。証明: `coreHead` の run を最初の動作で `RunsTo.bind` により分け、`hg` から `o = none` と `envAt w0 = envAt w`。残りは S1i の `ef_step`（`bind`/`pure`/`ite`/`letFun`/get/set/`throwError`、すべて既存の `EnvFrame` 補題と `CellPrem`）で閉じ、ログの `if none.isSome = true` を `if_neg` で `pure ()` にする。`HeadIO` は使わない。
- `counterLoop_final9P`: `counterLoop_final9` の `hhead` を `CellPrem` + `GetEnvProfileAt` に替えた形（`HeadIO`/`hio` なし）。仮説: `L lvl env₀ hstart hr hcell hg hread hgatesB hquote hreader`。
- 閉じていないこと: `hg` は仮説のまま（`unset` は実行時のプロセス環境、`env` は `IO.getEnv` の環境保存）。`hg` が供給できる経路は未確認で、不可能性も主張しない。profile 有効の run（`o = some _`）は、この形では**保証範囲外**。

### 19.4 (c) FREEZE DRAFT（未承認。台帳に数えない。C.EN-4/Laws に吸収しない。どの定理も使わない）

ログ枝を保証範囲に残す場合の義務。stderr callback と固定 Handle 操作を分ける:
```lean
def logStderrAct (msg : String) : IO Unit := do IO.eprintln msg; Sparkle.Compiler.flushStderr
def logTailAct   (msg : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/tmp/sparkle-profile.log" .append; h.putStrLn msg; h.flush
structure LogBranchDraft (mctx mref cctx cref) : Prop where
  stderrPreserves      : ∀ msg, EnvFrame (liftM (logStderrAct msg) : MetaM Unit) mctx mref cctx cref
  fixedHandlePreserves : ∀ msg, EnvFrame (liftM (logTailAct msg) : MetaM Unit) mctx mref cctx cref
```
- `stderrPreserves` は**現在の stderr stream** の `putStr`/`flush` callback（`setStderr` で差し替え可能、`eprintln` は現 stream の `putStr` を呼ぶ）が成功する限り env を書き換えない、という条件で、一般法則ではなく callback ごとの条件として明示する（所見C）。**訂正（S1q）**: 上記は意図の記述で、型としては `stderrPreserves : ∀ msg, EnvFrame (liftM (logStderrAct msg))` は特定の callback/world の条件を持たず、`EnvFrame` は ∀ world なので、「callback ごとの条件」にはなっていない。draft は**記述専用**で、型は条件を表さない。`fixedHandlePreserves` は固定パス・固定 Handle primitive だけの義務。
- 旧 `HeadIO.log`（`∀ msg, EnvFrame (liftM (profLogIO true msg))`）は上の 2 つの連言に分かれるが、`liftM` が IO の bind を MetaM の bind に写す等式（lift の法則）は証明できていないので、同値の定理は置かない（試したが未達。新しい law を足さないため）。
- 採用する場合は追加の未払い義務として差分を再照合する。現在は計上しない。

### 19.5 Check13 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck13`、913 jobs、exit 0）

- `FGCIRCUIT13 SIGNATURES`: `GetEnvProfileAt.mk`、`headAt_of_profileOff`、`counterLoop_final9P`、`LogBranchDraft.mk`（draft）の完全型を独立に書いて `isDefEq`（default 透過度）で照合し、binder の種類も一致。**21 mutant 棄却**: ログ枝を通る形（`o.isSome`）、独立 world からの lookup、end world で自明になる env 前提、unset/env/cell/frame の欠落、frame が無関係な world、結論が end world、旧 `HeadIO` を run 局所の frame の代わりにしたもの、final9P の frame/link/結論の end world、別 root の post、draft の stderr/handle 部分の欠落・flush 欠落・別パス。
- `FGCIRCUIT13 HYPS`/`REMAINING`: `headAt_of_profileOff` = `X hcell hg`、`counterLoop_final9P` = `L lvl env₀ hstart hr hcell hg hread hgatesB hquote hreader`。`HeadIO`/`hhead`/`hio`/`hquiet`/`hdRun`/`hsrc` は前提に無い。
- `FGCIRCUIT13 NOTUSED`: 2 定理の型と値が `HeadIO`・`LogBranchDraft`・`profLogIO`・`envFrame_coreHead`・`headAt_of_cellPrem` を直接参照しない。
- `FGCIRCUIT13 AXIOMS`: 2 名、標準 axiom のみ。

### 19.6 次

(1) `hg` の供給（`IO.getEnv` の run の結果・環境保存。コンパイル時の切替案 19.2-2 を採れば `unset` は消える）。(2) draft の採否（reviewer）。(3) 他の 3 root への `final9P` 相当の持ち上げ（counterLoop と同手順）。

## 20. S1p（Issue `sparkle-fg-circuit-pilot` の次の束）: 単一環境の carrier（M1）、意味保存の経路（M2）、`List.rec` の最初の小単位

土台 `e2301cd4`（par/fgc-s1）。追加ファイル（既存の定理は書き換えていない。コメント 2 箇所のみ訂正: `Tools/ShippingFGCircuitS1mCD.lean` 冒頭の「definitional equality」「has no derivation」）: `Tools/ShippingFGCircuitS1pCD.lean`、`Tests/Gen5/FGCircuitPilotCheck14.lean`（lakefile 登録は各 1 回）。TRUSTED・axiom・sorry・native_decide・新しい law はない（`FGCIRCUIT14 AXIOMS`: 29 名、標準 axiom のみ）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。Issue の状態は変えていない。`Sparkle/Compiler/*` と HeadIO 関連ファイルには触れていない。

### 20.1 M1: 公開 carrier を 1 環境にした

S1m の `CircCVX env := fun env' X α v => … env'.find? X … CDX env [] d.value …` は引用を `env'` で読み、展開を `env` で行うため、**型の上では別環境を許す**（`circCV_to_X` だけが同じ `env`）。S1p:

- `CircCVS : ConstValueRel := fun env X α v => ∃ d, env.find? X = some (.defnInfo d) ∧ d.levelParams = [] ∧ CDX env [] d.value α v`。引用と展開が**同じ変数 `env`**。
- 橋: `circCV_to_S : CircCV env X α v → CircCVS env X α v`（`cdx_of_cd`）、`circCVS_to_X`、`circCVX_iff_S`（`env' = env` の下で `CircCVX env env'` と `CircCVS env'` が同値。仮定が要る）、`circCVS_functional : ConstValueFunctional CircCVS`（`cdx_fun`）、`sourceDenotes_to_S`、`declConnect_to_S : DeclConnect CircCV env₀ P Tgt → DeclConnect CircCVS env₀ P Tgt`。
- **run 側**: `CircCVSAt cref w X α v := CircCVS (envAt cref w) X α v`。`circCVS_at_of_getEnv`: `RunsTo getEnv … w e w'` から `CircCVS e X α v ↔ CircCVS (envAt cref w) X α v`（`getEnv_value`。**開始 world `w`** であって終了 world `w'` ではない）。`HftObCDX env := CDX env [] hftRootValue (MonoTy shHft) synth_hftPcieOutByte`、`circCVS_hft_of_obCDX`、`circCVS_hft_run`（`env := envAt cref w`）。`HftObCDX` は**型だけで未供給**（`hcd` の供給ではない）。
- **別 env の負対照**（kernel の定理）: `circCVX_mixed`: `EnvDefs env (Δn 5)`（`mini := pure 5`）、`env'` が `X := mini` を宣言していれば、`env'` が何であれ `CircCVX env env' X (pure 5)` が成り立つ。`circCVS_rejects_mixed`: `EnvDefs env' (Δn 6)`（`env'` の `mini := pure 6`）なら `¬ CircCVS env' X (pure 5)`（`cdx_eq` と `Signal.pure` の単射性）。`miniDen 6` で `CircCVS env' X (pure 6)` は導出できる（Check14 の `circCVS_pos`）。つまり S1m の carrier は混在対を通し、単一環境の carrier は通さない。

### 20.2 M2: 意味保存の経路（§17.8 に書いた）

§17 の「健全性（定義的等式）」「新規則は値を変えない」「導出が存在しない」を撤回し、§17.8 に (a) 型の正しい入力に対する縮約の意味保存、(b) 対象 root で元の Lean 項と展開後の項の等式証明をカーネルに渡す、の 2 経路を明記した。`cdx_fun` は新関係の一意性、21 件の比較は監査、`projCtor` は raw `Expr` 規則、`EnvDefs`/`EnvCtors` は追加の未供給内容。

### 20.3 再帰子の最初の小単位（`List.rec` だけ）

方針（reviewer）: 汎用 `recInfo` 解釈・universe の拡張はしない。`runCircuitH` の `List.rec` で major が静的に `nil`/`cons` に展開できる範囲だけ。有限の回路構築リストを展開する。実行時の無制限 `List` を回路にしない。新 TRUSTED なし。

- `recStep env e`: 頭が定数 `List.rec`、`env.find? List.rec = some (.recInfo _)`、引数が 5 個以上（`α motive nilc consc major extra…`）、`major` が `recMajorWh`（`whStep` を最大 256 回）で `List.nil _` / `List.cons _ h t` に至るとき: nil なら `betaApp nilc extra`、cons なら `betaApp consc ([h, t, List.rec.{ls} α motive nilc consc t] ++ extra)`。**宇宙の水準 `ls` は入力のまま**（拡張なし）。他の再帰子（`Nat.rec`）、`casesOn`、部分適用、変数の major（`bvar`）では `none`（Check14 RECSTEP の対照）。major が constructor まで出ない箇所は `none` で止まり、`MISSING` にその major の形が出る（`describeRecStuck`）。
- 規則: 新しい帰納族 `DY env`（`DX` の全規則 + `recIota`。`DX` は編集していない。`dx_to_dy : DX env ρ e r → DY env ρ e r`）。`recIota`: `appFn e = List.rec ls`、`env.find? List.rec = recInfo ri`、`recStep env e = some e'`、`CDY env ρ e' α v` → `CDY env ρ e α v`。**`beta` と `projStep` は `headRedexR`/`whStepR` 上に置いた**（`whStep` に「射影の引数が `List.rec` の redex のとき射影の内側で `recStep`」を足しただけ。`whStepR_of_whStep`・`headRedexR_of_headRedex` で `DX` の導出はそのまま入る）。`List.rec` が射影の引数にだけ現れる hftPcie の形（`brecOn` の `PProd#0`）に必要。
- 関数性: `dy_fun`、`cdy_fun`、`tdy_fun`、`cdy_eq`、`circCVY_functional`（導出に関する `induction`。衝突の反駁に `recStep_head`、`unfoldAt_rec`、`headRedexR_rec`、`whStepR_ctor`）。仮定なし。
- **元の項との証明（経路 (b)）**: 規則 `recIota` の値は展開後の式の値であり、元の項との一致は**最終の型付けで検査される**: `HftObCDX` の `v` は `synth_hftPcieOutByte`（元の Lean 定数）で、規則が組む値がこれとカーネルで定義的に等しい導出だけが型検査を通る。その際 `List.rec` の iota は Lean の等式として **すべての引数に対して `rfl`**: `listRec_nil_eq : List.rec n c [] = n`、`listRec_cons_eq : List.rec n c (a :: xs) = c a xs (List.rec n c xs)`（universe 多相のまま）。これらは**一般の意味保存定理ではない**（`Expr` の書き換えを意味に結ぶ定理は無い）。Check14 は走査が取った各ステップ（入力の `List.rec` spine、`recStep` の結果）を Lean の `isDefEq`（default 透過度）で照合する: **2 件（distinct）すべて定義的に等しい**（loose bvar は junk 型の fvar で閉じた。型付けの検査ではなく縮約の検査）。
- **フォールバック（`Circuit` の pure/bind/next の展開補題）**: iota が constructor に届かない部分項に備え、`Circuit.pure'`/`bind`/`next` の定義から `rfl` で証明した展開補題 `circuit_pure_eq`、`circuit_bind_eq`、`circuit_next_eq` を置いた。**今回のルートでは使っていない**（`List.rec` はすべて静的 major だった）。

### 20.4 hftRootValue の走査（Check14 SNAPSHOT14、1 環境の値）

`Check14` の recognizer は規則の関数（`unfoldAt`/`headRedexR`/`whStepR`/`recStep`/`instE`）そのままで root の値を走査する（証明ではなく走査）。

- **走査は 505 節点、`List.rec` の iota を 34 回（distinct 2: 17 箇所 × `cons`、`nil` の 2 段）取る**。S1m の stuck（`proj Prod#0 of proj Prod#0 (proj PProd#0 (List.rec …))` ×17）は消えた。走査の記録と `whStepR`/`headRedexR` の一致（不一致 0）。
- **新しい stuck（今回の走査はここで停止、導出は未供給）**: `Sparkle.Core.Signal.Signal.mk [constructor]` ×17。`mkRegList` の読み出し lens `Signal.map Prod.fst (readSig s)`（`Signal.map` を `unf` した `Signal.mk { val := fun t => … }` の構造体リテラル）。`CD` の primitive 14 頭に `Signal.map` も `Signal.mk` も無い。次の設計問題は「`Signal.map` を primitive とするか（`Prod.fst`/`Prod.snd` の関数値の `CD` が要る）、`Signal.mk` を `Signal` の値の規則にするか」で reviewer の判断を仰ぐ。`tdFail`: なし。
- したがって `HftObCDX`（`hcd`）は**今回も供給していない**。

### 20.5 Check14 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck14`、912 jobs、exit 0）

- `FGCIRCUIT14 SIGNATURES`: `CircCVS` の定義、`circCV_to_S`、`circCVS_at_of_getEnv`（`envAt cref w`）、`circCVX_iff_S`、`circCVS_functional`、`circCVX_mixed`/`circCVS_rejects_mixed`、`DY.recIota`、`DY.beta`/`DY.projStep`（`whStepR`/`headRedexR`）、`dx_to_dy`、`cdy_fun` を独立に書いた文面と `isDefEq`（default 透過度）で照合。**19 mutant 棄却**（carrier: 固定の環境、非空の valuation、宇宙パラメータ条件なし、`CDX` の環境の存在量化; 橋: 固定の環境; run: 終了 world `w'`; `iff_S`: 環境の一致なし; 関数性: `CircCV`; 混在対: 値の入替、`Δn` の入替; `recIota`: `Nat.rec`、recInfo なし、結論が `e'`、`unfoldAt`; `beta`/`projStep`: 旧 `headRedex`/`whStep`; 埋め込み: 逆向き; `cdy_fun`: 別 env、`HEq` なし）。
- `FGCIRCUIT14 OLD RULES`: `DX` の 26 コンストラクタ（`beta`・`projStep` 以外）が `DY` で同一。対照（`sigMux` を `sigPure` と見る）は棄却。
- `FGCIRCUIT14 NEGATIVE CONTROL (different env)`: 2 つの具体環境（`mini := pure 5` / `pure 6`、`X := mini`）を `addDecl` で作り、同じ引用が `unfoldAt` で別の値に展開されることと、`EnvDefs` の行の一致（meta 評価）を確認。
- `FGCIRCUIT14 RECSTEP`: nil/cons/ih/2 段/extra 引数/beta した major の各ケースが期待どおり。変数の major、`Nat.rec`、部分適用、`List.casesOn` は step しない。水準は保たれる。
- `FGCIRCUIT14 AXIOMS`: 29 名、標準 axiom のみ。
- `FGCIRCUIT14 SNAPSHOT14`/`MISSING`/`TRACE`: 20.4 のとおり。equation check（Lean `isDefEq`）: 2 件中 2 件、不一致 0、例外 0。

### 20.6 証明したもの / 名前付きの仮説・未供給 / 数え方

- **証明した**: `circCV_to_S`、`circCVS_to_X`、`circCVX_iff_S`、`circCVS_functional`、`sourceDenotes_to_S`、`declConnect_to_S`、`circCVS_at_of_getEnv`、`circCVS_hft_of_obCDX`、`circCVS_hft_run`、`circCVX_mixed`、`circCVS_rejects_mixed`、`dx_to_dy`、`dy_fun`/`cdy_fun`/`tdy_fun`/`cdy_eq`、`circCVS_to_Y`、`circCVY_functional`、`whStepR_of_whStep`、`headRedexR_of_headRedex`、`whStepR_ctor`、`listRec_nil_eq`、`listRec_cons_eq`、`circuit_pure_eq`/`circuit_bind_eq`/`circuit_next_eq`。
- **名前付き仮説／未供給（新規に増えたもの・変わらないもの）**: `HftObCDX`（型のみ、`hcd` 未供給）。`EnvDefs`/`EnvCtors`（実 run 環境について追加の未供給内容）。規則の意味保存（§17.8 の経路 (a)/(b)。(b) は受理される導出が未供給の間は未供給）。`recStep` と Lean の `List.rec` の対応は、Check14 の `isDefEq` による走査ステップの監査であって定理ではない。`Signal.mk`/`Signal.map` の規則（20.4）。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付きは減算しない。

### 20.7 次

(1) `Signal.map`／`Signal.mk` の規則の設計（reviewer）。(2) その後 `hcd` の導出が `HftObCDX` に届くか走査し直す（各ステップの等式は経路 (b) でカーネルに渡す）。(3) `HftObSrc`/`HftObTopCore`/`HftObNoRaw` は別。

## 21. S1q（Issue `sparkle-fg-circuit-pilot` の次の束）: プロファイル無効の入口（`profile = false` を純粋に固定）— 設計と 4 leaf root の前提差分

土台 `e2301cd4`（par/fgc-s1）。Issue の状態は変えていない。S1p のファイル（`Tools/ShippingFGCircuitS1pCD.lean`、§17/§20、Check14）には触れない。reviewer 裁定（§19.2-2 の実装）: `GetEnvProfileAt` は名前付きの run 局所条件のまま（供給でも縮約でもない）。この束は compiler 変更で、**保証対象の入口**の `profile` を `false` に固定し、その `coreHead` に `IO.getEnv` もログ実行も無い形にする。成果は引き続き**条件付き**。台帳に数えない。

### 21.1 訂正（§19.2-2 / §19.4）

- §19.2-2: `Options` へ移すだけでは `profile = true` 枝のログは `coreHead` に残る（消えるのは `IO.getEnv` の 1 件だけ）。ログ枝が消えるのは `profile` が `false` に**固定**されたときだけ。§19.2 本文に訂正を入れた。
- §19.4: `LogBranchDraft` は記述専用。`stderrPreserves` は `∀ msg, EnvFrame (liftM (logStderrAct msg))` で、`EnvFrame` は ∀ world。特定 callback/world の条件を型に持たないので「callback ごとの条件」ではない。`fixedHandlePreserves` も同様に ∀ world。draft は採否の判断対象に上げず、無効経路を優先する。

### 21.2 compiler の設計（実装は §21.4 の後。`Sparkle/Compiler/Elab.lean` に小さく追加、既存の定義は 1 文字も変えない）

`Elab.lean` の既存定義（`synthesizeCombinationalCoreWith`/`…Core`/`synthesizeCombinationalWith`/`synthesizeCombinational`/`synthesizeChild`/`sparkleChildSynth` の `initialize`）は**そのまま**。約 30 本の既存 Tools 定理が `unfold synthesizeCombinationalCore synthesizeCombinationalCoreWith` で展開するので、引数追加や wrapper 化は避ける（測定: 展開側 30 ファイル超）。追加するのは 3 定義（翻訳器の結び目の後でないと書けないので `Elab.lean` 内、`synthesizeChild` の直前）:

```lean
/-- the guaranteed entry: `synthesizeCombinationalCoreWith … declName [] false true` with `profile := false` FIXED (no IO.getEnv, no log) -/
def synthesizeCombinationalCoreOff (declName : Name) : MetaM (Module × Design)
/-- `synthesizeCombinationalWith` over it (same post-processing) -/
def synthesizeCombinationalOff (declName : Name) : MetaM (Module × Design)
/-- command level: the setting is read OUTSIDE the entry; the guarantee starts after it -/
def synthesizeEntry (declName : Name) : MetaM (Module × Design) := do
  if (← IO.getEnv "SPARKLE_PROFILE").isSome then synthesizeCombinational declName   -- diagnostic path: OUTSIDE the guarantee
  else synthesizeCombinationalOff declName                                         -- guaranteed path
```
- `#synthesize`/`#synthesizeVerilog`/`#showVerilog` は `synthesizeCombinational` の代わりに `synthesizeEntry` を呼ぶ（3 箇所）。`SPARKLE_PROFILE` 設定時は従来と**完全に同じ**経路（診断経路。保証の外と明記）。未設定時は `profile = false` の従来経路と同じ出力（§21.6 の比較で確認）。通常の IP の成功範囲は狭めない（ログ枝は未設定時に実行されないので、成功・出力は同じ）。
- `Off` の本体は `synthesizeCombinationalCoreWith` の `parameters := []`, `symbolicMode := false`, `certifiedFrontEnd := true`, `profile := false` の特殊化で、`logProf := fun _ => pure ()`。`IO.getEnv "SPARKLE_PROFILE"` も、`IO.eprintln`/`flushStderr`/`Handle.mk` も出てこない。`synthesizeFromConst` に渡す `logProf` は no-op。
- 範囲外（変更しない）: `synthesizeHierarchical`（`#synthesizeDesign` 等）、`synthesizeCombinationalWithParameters`、`synthesizeChild`/`sparkleChildSynth` の `initialize`。子の入口は引き続き診断入口（`profile` を読む）。これは `ShippingInitFrame`/`ShippingStartAtLoad` が `initialize … (some synthesizeChild)` を手で模型化しているため、`initialize` を変えると模型との対応が崩れるからで、**非 leaf root（`synth_hftPcieOutByte`）の子**はこの束の保証対象の外のまま（子の profile 読み取りは `HeadIO`/`GetEnvProfileAt` の問題としてそのまま残る）。4 leaf root は子を持たない。
- 副作用: `Elab.lean` が変わるので、依存する全モジュールが再ビルドされる。

### 21.3 Tools 側（新ファイルだけ。既存の定理・定義は変えない）

- `Tools/ShippingFGCircuitS1qLinked.lean`: `coreHeadOff`/`coreRestOff`（`coreHead`/`coreRest` から `IO.getEnv` と `logProf` を除いた鏡像。`CoreSaved.profile := false`）、`core_eqOff`/`core_splitOff`/`core_chainOff`、`MachineDefinesLinkedOff`（`profLogIO s.profile` の所を no-op に）、`synthesizeCombinationalCore_machine_soundCOff`、`machineRunJQC_of_closesCOff`（`coreHeadOff_jqcA` を含む）、`Linked2` の 5 本の写し、`postEntryOff`/`synthesizeCombinational_checkedOff`、`PostRunOff`、`leaf_*_of_runCOff`、`hTop_of_leaf4Off`、`X_artifact_atCOff`、`X_final4DOff`。写しは証明本体を変えず、`synthesizeCombinationalCore`→`…Off`、`coreHead`→`coreHeadOff`、`MachineDefinesLinked`→`…Off`、`PostRun`→`…Off` の置換のみ（機械的）。
- `Tools/ShippingFGCircuitS1qHead.lean`: `HeadAtOff`、`envFrame_coreHeadOff`（**`CellPrem` だけ**から。`HeadIO` も `GetEnvProfileAt` も使わない）、`headAtOff_of_cellPrem`、`X_final10Off`、`X_final12`（4 root）。
- `Tests/Gen5/FGCircuitPilotCheck15.lean`: 独立に書いた完全型の `isDefEq`、mutant、HYPS、NOTUSED、AXIOMS。`Tests/Gen5/FGCircuitPilotCompare15.lean`: 出力比較用（§21.6）。

### 21.4 新しい head に載せた 4 leaf root の最終定理の型と前提の差分

最終定理は `X_final12`（X = counterLoop / shift4Loop / counterEnableLoop / arbiterSignal）。`X_final11`（S1l/S1n）との差分（counterLoop の例。他 3 root も同じ形、arbiter は `hB0 hcont` が加わるのは `X_final10` と同じ）:

| | `X_final11` + `headAt_of_profileOff`（S1o の `final9P` 系） | `X_final12`（S1q） |
|---|---|---|
| 入口の run `hr` | `RunsTo (synthesizeCombinational ``X)` | `RunsTo (synthesizeCombinationalOff ``X)` |
| head の前提 | `hhead : HeadAt X w`。供給は `CellPrem` + `GetEnvProfileAt mctx mref cctx cref w`（`unset`: getEnv の結果が `none`、`env`: getEnv が env を保つ）、または `CellPrem` + `HeadIO`（S1i） | **無い**。`HeadAtOff` は `CellPrem` だけから証明する |
| cell の前提 | `hcell : ReadWorld cref`（`CellPrem` の 1 成分） | `hcell : CellPrem MkRefd mref cref`（C.EN-4 の既存の束。`ReadWorld cref` を含む） |
| 結論の post | `PostRun mctx mref cctx cref w ``X D' b raw`（`synthesizeCombinationalCore` の run を含む） | `PostRunOff …`（`synthesizeCombinationalCoreOff` の run を含む） |
| その他 | `L lvl env₀ hstart hlvl hx hf hlink`（arbiter は `hB0 hcont` も） | **同じ**（`L lvl env₀ hstart hlvl hx hf hlink`、arbiter は `hB0 hcont` も） |

消える前提: `GetEnvProfileAt`、`HeadIO`（getEnv の `EnvFrame` 1 件と、profile ログの `EnvFrame` ∀msg の 1 件）、`hhead`。**置き換わる前提**: なし（`CellPrem` は既に S1o の `final9P` にあった）。つまり前提の数は減るが、`GetEnvProfileAt` の `unset` は「消えた」のであって「供給された」のではない: 保証は `SPARKLE_PROFILE` 未設定のコマンド経路（`synthesizeEntry` の `else` 枝）についてだけで、設定時の経路（診断）は保証の外。この区別は `synthesizeEntry` の `if` が入口の**外**にあることで型に出る（`X_final12` は `synthesizeCombinationalOff` の run について語り、`synthesizeEntry` の run については語らない）。`synthesizeEntry` の `else` 枝が実際に実行されたことは、`IO.getEnv` の結果 `none` の観測でありこの束では供給しない（run 局所の観測。名前付きのまま）。

残る名前付き仮説（不変）: `RootExtern`/`RootEnvFacts`/`hlvl`/`ReadsAt`（`hlink`）、`Laws`/`Start`/`hr`、`CellPrem`、arbiter の `BoundaryRowsInEnv`/`ContainsAt`。非 leaf の `hcd`/`hsrc`/`htop`/`hnoraw` は未供給。`EnvDefs`/`EnvCtors` は実 run 環境については未供給（S1m の裁定どおり）。

### 21.5 実装と測定（compiler diff・既存 Tools への影響）

**compiler diff（`Sparkle/Compiler/Elab.lean` のみ、追加 106 行・変更 3 行）**: 追加は `synthesizeCombinationalCoreOff`（`synthesizeCombinationalCoreWith … [] false true` の `profile := false` 固定の特殊化。`IO.getEnv "SPARKLE_PROFILE"` も `IO.eprintln`/`flushStderr`/`Handle.mk` も無く、`logProf := fun _ => pure ()`）、`synthesizeCombinationalOff`（`synthesizeCombinationalWith` と同じ後処理）、`synthesizeEntry`（`SPARKLE_PROFILE` を入口の**外**で読み、設定時は従来の `synthesizeCombinational`＝診断経路、未設定時は `synthesizeCombinationalOff`）。変更は `#synthesize`/`#synthesizeVerilog`/`#showVerilog` の 3 箇所の呼び出し（`synthesizeCombinational declName` → `synthesizeEntry declName`）だけ。既存の定義・`initialize`・他のコマンドは 1 文字も変えていない。新ファイルにしなかった理由: `Off` は翻訳器の結び目（`translateExprToWire`/`synthesizeFromConst`）の後でないと書けず、`Elab` のコマンドが呼ぶので、`Elab` が import する側のファイルには置けない。

**Tools 側（新ファイルのみ）**: `Tools/ShippingFGCircuitS1qLinked.lean`（`coreHeadOff`/`coreRestOff`、`core_eqOff`: `synthesizeCombinationalCoreOff = coreHeadOff >>= coreRestOff` が `rfl` で閉じる、`core_chainOff`、`coreHeadOff_jqcA`、`MachineDefinesLinkedOff`、`machine_run_of_coreCOff`、`machineRunJQC_of_closesCOff`、`synthesizeCombinationalCore_machine_soundCOff`）、`Tools/ShippingFGCircuitS1qEndpoint.lean`（`Linked2`/`Final4`/`Roots4`/`S1iRoots` の写し: stream/loop/wired endpoint、`hTop_of_leaf4Off`、`X_artifact_atCOff`、`X_final4DOff`、`PostRunOff`、`postEntryOff`、`synthesizeCombinationalOff_checked`。証明本体は機械的な改名のみで編集していない）、`Tools/ShippingFGCircuitS1qHead.lean`（`envFrame_coreHeadOff`・`headAtOff_of_cellPrem`: **`CellPrem` だけ**から。`X_final10Off`、`X_final12`）。

- **`HeadAt` は `CellPrem` だけから証明できた**（新しい head には getEnv もログも無く、S1i の `ef_step` 分解がそのまま通る）。`HeadIO`/`GetEnvProfileAt`/`hhead` は不要。
- 4 root の最終定理 `X_final12`: 前提は `L lvl env₀ hstart hr hcell hlvl hx hf hlink`（arbiter は `hB0 hcont` も）、`hr` は `synthesizeCombinationalOff` の run、`hcell : CellPrem MkRefd mref cref`。差分は §21.4。
- 既存の定理への影響: **既存の定義・定理は変更なし**。`Elab.lean` が変わるので全依存モジュールが再ビルドされる。再ビルドした既存ターゲット（`kjob lake build`、Elab 変更後）: `Tests.Gen5.FGCircuitPilotCheck13`（913 jobs）、`Check12`（913）、`Check11`（911）、`Check10`（911）、`Check9`（916）、`Check8`（909）、`ClosingRunCheck`（756）、`RunReadsCheck`（748）、`Flow1ReadsCheck`（843）、`DCEntryCheck`（746）、`Tools.ShippingEntrySoundness`（248）、`Tools.ShippingMachineOutcomeA3`（349）、`Tools.ShippingChildPinC`（339）、`Tools.ShippingLeafKeepCache`（599）、`Tools.ShippingMemoLawsWith`（318）— すべて exit 0。保存ログの Check 行は変更前と同じ（Check10 AXIOMS 13、Check11 16、Check12 24、Check13 2）。**失敗が 1 件**: `Tools.ShippingGen4ParamEntry` が `core_symbolic_reads`（216 行）で `(deterministic) timeout at whnf, maximum number of heartbeats (1600000)`。**土台 `e2301cd4` の単独ビルドでも同じ行で同じ失敗**なので、この束の変更による退行ではなく既存の問題（未対処。S1q では触れない）。`synthesizeCombinationalCore`/`…Core`/`coreHead` を `unfold` する約 30 の Tools ファイルは、それらの定義が不変なので影響を受けない（これが「既存の head を残す」案を採った理由）。
- `Off` と従来経路の同一性: Lean の定理としては `core_eqOff`（`Off` の構造）と、§21.6 の出力比較（5 root の IR/SV が完全一致）で確認する。従来の `coreHead` で `getEnv` の結果が `none` のときと `Off` が同じ run になる、という形の定理は置かない（`IO.getEnv` の結果が `none` である run の存在を使うことになり、`GetEnvProfileAt` を別の名前で戻すことになるため）。

### 21.6 出力比較（4 root + hftPcie、IR と SV のテキスト）

`Tests.Gen5.FGCircuitPilotCompare15`（5 つの root: counterLoop、shift4Loop、counterEnableLoop、arbiterSignal、hftPcieLoop.outByte に `#synthesize`＝IR と `#synthesizeVerilog`＝SV）のビルドログから、`scripts/gen5/fgc_s1q/extract.sh` でこのモジュールの出力だけを取り出して比べた。変更前（土台 `e2301cd4`）と変更後（`SPARKLE_PROFILE` 未設定の pod）で **1312 行が完全に一致**（`diff` 空）。hftPcie は非 leaf で、子の入口は従来の診断入口のまま（上位だけ `Off`）で、出力は同じ。

### 21.7 結果・S0 baseline で比べるもの

**Check15**（`kjob lake build Tests.Gen5.FGCircuitPilotCheck15`、918 jobs、exit 0）:
- `FGCIRCUIT15 SIGNATURES`: `core_eqOff`、`envFrame_coreHeadOff`、`headAtOff_of_cellPrem`、`counterLoop_final12`、`shift4Loop_final12`、`counterEnableLoop_final12`、`arbiterSignal_final12` の完全型を独立に書いて `isDefEq`（default 透過度）で照合し、binder の種類も一致。**45 mutant 棄却**（診断入口 `synthesizeCombinational` の run、旧 `PostRun`、`CellPrem` の代わりに `ReadWorld` だけ、cell 前提の欠落、取り除いた `GetEnvProfileAt`/`HeadIO` を戻したもの、旧 `coreHead`、end world の link/結論/frame、別 root の post、lvl/extern/facts/boundary 前提の欠落）。mutant は正規化後の式が構文的に異なり、かつ reducible 透過度で defeq でないことで棄却している（default 透過度の探索は両入口の定義を深く展開して終わらないので行わない。`same` 側は default）。
- `FGCIRCUIT15 HYPS`: 4 本の `X_final12` = `L lvl env₀ hstart hr hcell hlvl hx hf hlink`（arbiter は `hB0 hcont` も）、`headAtOff_of_cellPrem`/`envFrame_coreHeadOff` = `X hcell`。`hhead`/`hg`/`hio`/`HeadIO`/`GetEnvProfileAt` は前提に無い。
- `FGCIRCUIT15 NOGETENV`: `coreHeadOff` が `Sparkle.*`/`Tools.*` で到達する 26 個の定数に `IO.getEnv`・`IO.eprintln`・`IO.FS.Handle.mk`・`flushStderr`・`profLogIO`・文字列 `"SPARKLE_PROFILE"`・`"/tmp/sparkle-profile.log"` が無い。`synthesizeCombinationalCoreOff` と `coreRestOff` の値にも無い。対照: 旧 `coreHead` はこれらに到達し、`synthesizeCombinationalCoreWith` は文字列を持ち、`synthesizeEntry` は `SPARKLE_PROFILE` を入口の外で読んで 2 つの入口を振り分ける。
- `FGCIRCUIT15 NOTUSED`: 4 本の最終定理 + `headAtOff_of_cellPrem` + `envFrame_coreHeadOff` の値が `Tools.ShippingFGCircuit*` で到達する 293 個の定数のどれも `coreHead`/`HeadIO`/`GetEnvProfileAt`/`headAt_of_profileOff`/`envFrame_coreHead`/`headAt_of_cellPrem` に触れない。うち S1q の 51 個は旧入口・診断入口（`synthesizeCombinationalCore`/`…With`/`synthesizeCombinational`/`synthesizeCombinationalWith`/`synthesizeEntry`）に触れない。（`Tools.*` 全体への走査（4793 個）でも同じ結果を得たが、ビルドに 10 分かかるので範囲を狭めた。）
- `FGCIRCUIT15 AXIOMS`: 6 名、標準 axiom のみ。

**出力比較**: §21.6。**証明できたもの**: `HeadAt` の新しい head 版 `headAtOff_of_cellPrem`（`CellPrem` だけ）、4 root の最終定理 `X_final12`。**名前付き仮説のまま**: §21.4 末尾。**追加で名前付きにしたもの**: なし（`GetEnvProfileAt`/`HeadIO` は消えた。実環境で `else` 枝が選ばれたこと（`SPARKLE_PROFILE` 未設定）は保証の仮説ではなく、保証は `synthesizeCombinationalOff` について）。

**S0 の必要 IP baseline（`scripts/gen5/fgc_baseline/capture.sh`、327 コマンド）で比べるもの**（coder が別に実行）:
1. `SPARKLE_PROFILE` 未設定で、各コマンドの終了コード・stdout の IR/SV テキスト・stderr の警告（DRC など）を、土台 `e2301cd4` の capture と**バイト単位で比べる**。違いが出るはずがないもの: `#synthesize`/`#synthesizeVerilog`/`#showVerilog` は `Off` を通るが、本体は `profile = false` の従来経路と同じ。
2. `#synthesizeDesign`/`#writeVerilogDesign`/パラメータ付きコマンド等（`synthesizeHierarchical`/`synthesizeCombinationalWithParameters` を通るもの）は診断入口のまま（コードは不変）。これらも同じ出力のはず。
3. `SPARKLE_PROFILE=1` を付けた数本（`counterLoop`、hftPcie）で、stderr と `/tmp/sparkle-profile.log` の `[profile] …` 行の列が土台と同じ（診断経路が不変であること）。`#synthesizeVerilog` 自身が最初に出す `[profile] #synthesizeVerilog entry …` の行は従来どおり、`[profile] synthesizeCombinational … entering` 以降は診断入口が出す。
4. 実行時間: `Off` は `getEnv` 1 回とログ no-op クロージャの呼び出しを減らすだけで、差はノイズの範囲のはず（遅くなっていないこと）。
5. 失敗するコマンド（意図したエラー）も、メッセージが同じこと。`Off` の `throwError` は従来と同じ文言（`hardware modules nested deeper …`、`entryInlinerError?`）。
6. 非 leaf（子を持つ）root: 上位は `Off`、子は `sparkleChildSynth`＝`synthesizeChild`＝診断入口のまま。子の `profile` 読み取りは残る（§21.2）。出力は同じはず。

**次**: (1) `X_final12` の非 leaf root への持ち上げと、子の入口（`synthesizeChild`）の profile 固定（`initialize` の模型 `ShippingInitFrame`/`ShippingStartAtLoad` との対応を保つ形で）、(2) `synthesizeEntry` の `if` が `else` に落ちること（`SPARKLE_PROFILE` 未設定）を、保証の外の run 観測として明記し続けること、(3) 既存 Tools の `coreHead` 系定理を `Off` 版へ一般化する案（head を引数にした一般化）は、Check の固定した型を変えるので採らなかった。

## 22. S1r（Issue `sparkle-fg-circuit-pilot` の次の束）: `Signal.map Prod.fst/snd` の狭い配線規則、CDY/CDZ の単一 env 接続、Check の fail-closed 化

土台 `9a2ef5cd`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS1rCD.lean`、`Tests/Gen5/FGCircuitPilotCheck16.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない（`FGCIRCUIT16 AXIOMS`: 37 名、標準 axiom のみ）。Issue の状態は変えていない。S1q の領域（Compiler profile、S1qHead、Check15、§21）には触れていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は**条件付き**。

### 22.1 設計（reviewer 裁定に従う）

`Signal.mk` 一般則・`Signal.map` 本体の解釈・汎用高階関数・universe 拡張は**入れていない**。新しい帰納族 `DZ env`（`DY` + 下記）。`dy_to_dz`（したがって `DX`/`CD`）で埋め込む。`DY`/`DX` は編集していない。

- 値の規則: `mapFst`（`Signal.map.{0} D (A×B) A (Prod.fst.{0,0} a b) s`、値は Lean の `Signal.map Prod.fst sv`）、`mapSnd`、`prodMk`、`unitVal`。型の規則: `prodTy`、`punitTy`。
- `unf`/`beta`/`projStep`/`projCtor`/`recIota` を**結果 `r : Res`（型または値）について一般化**（`HList αs` のような型を同じ delta/beta/射影/`List.rec` で展開するため）。`unf` の停止条件は `stopR r e`（値: 従来の `headStop`、型: 核の型頭 `Nat/Bool/DomainConfig/BitVec/Signal/Prod/PUnit` は展開しない）。`letE` に前提 `coreHead A = true` を追加（以前は型判定から出た。`zeta` との排他のため明示）。
- `projRec`: 構造体引数が `List.rec` の redex である射影を、その場で `recStep`（`whStepR` は別の射影/適用の下でしか進めないため。型位置の `PProd#0 (List.rec …)` で必要になった）。
- **排他性**: `mapFst`/`mapSnd` は前提 `MapStuck env e`（`e` の `unfoldAt` が `Signal.mk` 頭の項になり、`Signal.mk` が `env` の `ctorInfo`）を持つ。`unf` が同じ式に適用されても `Signal.mk` 頭の項に導出が無いこと（`dz_signalMk_false`、`mapStuck_unf_false`）で衝突しない。`prodMk`/`unitVal` は `ctorInfo` を前提にして `unf` と衝突しない。
- **Lean の等式（全信号・全時刻、`rfl`）**: `signal_map_fst_at`/`signal_map_snd_at`（`(Signal.map Prod.fst sv).val t = (sv.val t).1` 等）、`signal_map_eq`、`signal_mk_fst_eq`/`snd_eq`（展開後の `Signal.mk` 本体が規則の値）、`signal_map_pair_at`、`signal_ext'`。値は元のソースの `Signal.map` から作り、生成 IR から定義していない。
- **関数性**: `dz_fun`/`cdz_fun`/`tdz_fun`/`cdz_eq`（導出に関する `induction`、仮定なし。`whStepR_listRec` ほか新しい衝突補題）。`circCVZ_functional`。

### 22.2 CDY/CDZ の単一 env 接続（CDX は埋めない）

`HftObCDX`（S1p §20.7）は `CDX` であり、`recIota` を持つ導出では埋まらない。DX→DY→DZ の橋だけがあり、**CDY→CDX は仮定しない・証明もしない**（`HftObCDX` と `HftObCDY` が定義的に別であることを Check16 が検査）。

`CircCVY`（S1p）、`CircCVZ`、`HftObCDY env`、`HftObCDZ env`、`circCVY_to_Z`、`circCVS_to_Z`、`SourceDenotesY/Z`、`sourceDenotesS_to_Y`/`Y_to_Z`、`declConnect_of_cv`、`declConnect_S_to_Y`/`Y_to_Z`、`circCVY_hft_of_obCDY`/`circCVZ_hft_of_obCDZ`、run 側 `circCVY_at_of_getEnv`/`circCVZ_at_of_getEnv`（**開始 world `envAt cref w`**）、`circCVY_hft_run`/`circCVZ_hft_run`。消費側の完全型: `HftFinalStmtWith Ob`（S1k の `HftFinalStmt` の写しで `hcd : Ob (envAt cref w)`）、`HftFinalStmtY`/`HftFinalStmtZ`、`hftFinalStmtWith_const`（`Ob := fun _ => HftObCD` で `HftFinalStmt` に一致 = 写しの忠実性、`rfl`）。いずれも**型のみで未供給**（`hcd` の供給ではない）。

### 22.3 Check16 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck16`、exit 0）

- `SIGNATURES`: 新規則・変更した規則・`dy_to_dz`・`cdz_fun`・`CircCVZ`・`HftObCDY/Z`・`circCVZ_at_of_getEnv`・`signal_map_*_at` を独立に書いた文面と `isDefEq`（default）で照合。**31 mutant 棄却**（関数の入替、型引数の取り違え、`MapStuck` 欠落、結論の取り違え、ctor 条件欠落、stop 条件の入替、`coreHead` の欠落/反転、`recInfo` 欠落、別 env、`HEq` 欠落、DX/DY の取り違え、終了 world、時刻のずれ ほか）。`OLD RULES`: 23 コンストラクタが DY と DZ で同一。
- `PATTERN`: 実際の Lean の elaborator が `Signal.map Prod.fst s`/`Prod.snd s` に作る Expr が規則の型と一致（レベル・引数順）。展開が `Signal.mk` 頭になり `MapStuck` が成立。入替は棄却。
- `AUDIT CONTROLS`: 判定関数 `Audit.verdict` が、不一致ペア（map fst と map snd、正しいペア混在でも）、空の対象集合、traceMismatch、例外、ok≠total、Nat と Bool を**棄却**し、正しい一歩と全 ok を受理。
- **fail-closed**: 実走査の等式監査は `bad = err = traceMismatch = 0` かつ対象ペア非空でなければ `throwError`（build が落ちる）。結果: **9 ペア（`List.rec` 8 distinct + `Signal.map` 1 distinct）、ok 9、bad 0、err 0、traceMismatch 0**。Check14 の logInfo 止まりを置換。**これは監査**: 閉じていない束縛変数を型 `Nat` の junk fvar で閉じた `isDefEq` であり、型付きの導出ではない。§17.8(b) を使っても、元の root 値への型付きの導出/等式がカーネルで完成するまで**意味保存済みとは呼ばない**。
- `AXIOMS`: 37 名、標準のみ。

### 22.4 SNAPSHOT16（hftRootValue、1 環境の値。走査であり証明ではない）

2388 節点。`List.rec` の iota 272 回（distinct 8、うち `projRec` 102 回）、`mapFst` 17 箇所（distinct 1）、`mapSnd` 0、`MapStuck` 不成立 0、`prodTy` 51、型レベルの展開 510（`HList`、`List.brecOn`、`List.casesOn`、`HList.match_1` ほか）。S1p の stuck（`Signal.mk` ×17、型位置の `PProd#0 (List.rec …)`）のうち、`Signal.map Prod.fst` 由来の `Signal.mk` と `HList` の型展開は進んだ。

**次の stuck（今回の走査はここで停止、導出は未供給）**:
1. `Signal.mk [constructor]` ×17: `(fun x1 x2 => (x1, x2)) <$> Signal.register … <*> …`（`packRegister` の `bundle2`＝`Signal.seq`/`Signal.ap` の展開）。2 引数関数の `Signal.map`/`ap` で、Prod.fst/snd の狭い規則の外。reviewer の「汎用高階関数にしない」に照らし、`bundle2`（2 つの `Signal` から `Signal (A×B)` を作る配線）を同じ狭さの規則にするか、reviewer 判断。
2. `Inhabited.mk [constructor]` ×17: `instInhabitedProd` ＝ `⟨(default, default)⟩`（`Signal.loop` の `inst` 引数）。`Inhabited` 構造体値の規則（と `default` の射影）が要る。

したがって `HftObCDZ`（`hcd`）は**今回も供給していない**。

### 22.5 証明したもの / 名前付き仮説・未供給

- **証明した**: 22.1/22.2 の定理（`dy_to_dz`、`dx_to_dz`、`dz_fun` ほか、`signal_map_*`、`circCVZ_functional`、`declConnect_*`、`hftFinalStmtWith_const` など）。
- **名前付き仮説/未供給**: `HftObCDX`/`HftObCDY`/`HftObCDZ`（型のみ）、`EnvDefs`/`EnvCtors`、規則と元ソースの意味の接続（`recStep`/`MapStuck` 等の Expr 書き換えの意味保存は定理ではなく監査）、非 leaf の `hsrc`/`htop`/`hnoraw`。上記 2 つの stuck。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付きは減算しない。

### 22.6 次

(1) `bundle2`/`Signal.ap` の狭い規則と `Inhabited` 構造体値の規則の設計（reviewer）。(2) その後 `HftObCDZ` に届くか走査し直す。

## 24. S1t（Issue `sparkle-fg-circuit-pilot` の次の束）: 非 leaf root `synth_hftPcieOutByte` の `Off` 入口上の最終文、新 carrier の結論、組み立ての証明

土台 `ba83ec10`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS1tFinal.lean`、`Tests/Gen5/FGCircuitPilotCheck18.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない。S1s の領域（`Tools/ShippingFGCircuitS1sCD.lean`、Check17、§23）には触れていない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**（名前付き仮説を残す）で、台帳に数えない。

### 24.1 reviewer 裁定への答え

裁定: `HftFinalStmtY/Z`（S1r §22.2）は型定義だけで、結論は旧 `RootArtifactMono`（`CD [] d.value`、環境なし）、run は旧 `synthesizeCombinational`。型を定義しても `CDZ → 旧 CD` も非 leaf の `Off` 接続も得られない。

この束でしたこと:
1. **結論側を明示的に更新した**。`SourceDenotesMonoV CV`/`RootArtifactMonoV CV`/`DeclConnectMonoV CV`/`FGCircuitConclusionMonoV CV`（`CV : CDRel := Environment → Expr → (α : Type) → α → Prop`、**環境を読む**単一 env の導出関係）。`CV := cdvOld`（`fun _ e α v => CD [] e α v`）のときは**旧定義と定義的に等しい**（`sourceDenotesMonoV_old`/`rootArtifactMonoV_old` は `Iff.rfl`）。`cdvX`/`cdvY`/`cdvZ` は `CDX/CDY/CDZ env []`。S1s の将来の family は `CDRel` を 1 つ足すだけで差し込める。
2. **run 側を `Off` に更新した**（上位 run = `synthesizeCombinationalOff`、コア義務は `synthesizeCombinationalCoreOff` と `MachineDefinesLinkedOff`、post は `PostRunOff`）。
3. **接続を証明した**（§24.3）: 名前付き義務から結論までの組み立て `synth_hftPcieOutByte_finalOff`。S1k の `synth_hftPcieOutByte_final` の `Off` + 新 carrier 版。
4. **`CDZ → 旧 CD` は提供せず、使わない**（`DZ` の規則（`recIota`・`mapFst` ほか）は `CD` に無いが、それは非導出性の証明ではない）。方向は `cdvOld → cdvX → cdvY → cdvZ` だけ（`cdvOld_to_X/X_to_Y/Y_to_Z/Old_to_Z`）。旧 carrier の結論は新 carrier の結論を含意する（`rootArtifactMono_to_Z`: old ⇒ new。4 leaf root の `X_final12` の結論をそのまま `DZ` 版に移せる）。new ⇒ old は今回は構成していない（逆向きは提供せず、使っていない。新しい規則があることは非導出性の証明ではなく、非導出性の定理は無い）。

### 24.2 最終文の完全な型（`HftFinalStmtOff Ob CV`）と、保証する範囲

```
HftFinalStmtOff (Ob : Environment → Prop) (CV : CDRel) : Prop :=
  ∀ {ι} {mref} {cref} (L : Laws mref cref) (lvl) (env₀) {mctx cctx w w' b D'}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem MkRefd mref cref)
    (hchk : CheckedStart lvl env₀ cref w hftRoot hftRootType hftRootValue synth_hftPcieOutByte.machineData)
    (hreadH : RootReader lvl (envAt cref w) hftHttp httpGetByte.machineData)
    (hreadT : RootReader lvl (envAt cref w) hftTlp tlpCplByte.machineData)
    (hcd : Ob (envAt cref w))
    (hsrc : HftObSrc lvl (envAt cref w))
    (htop : ∀ p, GPt lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hnoraw : HftObNoRawOff mctx mref cctx cref w b D'),
    (∃ raw, PostRunOff mctx mref cctx cref w hftRoot D' b raw) ∧
    ∃ (mm : MonoTy shHft) p, RootArtifactMonoV CV (envAt cref w) (GPt lvl (envAt cref w)) (PostRunOff … hftRoot D') hftRoot shHft mm b D' p
```
- `Ob` は carrier 義務（`HftObCDX/Y/Z` または S1s の family。型は `Environment → Prop`）、`CV` は結論の導出関係。両者の対応は文ではなく**定理の前提** `hOb : ∀ env, Ob env → HftObOf CV env`（`HftObOf CV env := CV env hftRootValue (MonoTy shHft) synth_hftPcieOutByte`）。`hftObOf_Y/Z`（`rfl`）で `HftObOf cdvY = HftObCDY`、`HftObOf cdvZ = HftObCDZ`。
- 上位 run は `Off`（保証対象の入口）。`hhead` は無い: `hcell : CellPrem` から `HeadAtOff`（S1q の `headAtOff_of_cellPrem`）と `ReadWorld` を出す。
- `HftObTopCoreOff`/`HftObNoRawOff` は S1k の `HftObTopCore`/`HftObNoRaw` の `Off` 版（`synthesizeCombinationalCore … [] false` → `synthesizeCombinationalCoreOff`、`MachineDefinesLinked` → `MachineDefinesLinkedOff`）。`hdRun` は `hchk`/`hcell` から導いて `htop` に渡す（前提ではない）。

**この文が保証すること**（4 義務と子の reader が与えられたとき）: `synthesizeCombinationalOff hftRoot` の run `(b, D')` について、(i) post を満たす `raw` が存在する、(ii) 開始 world の環境 `envAt cref w` の表から取れる package `p` があり、`p` は root の `machineData`（kD = 5）を持ち、(iii) root 宣言の値が**新 carrier の導出** `CV (envAt cref w) d.value (MonoTy shHft) mm` を持ち（`mm = synth_hftPcieOutByte`）、(iv) `p.src` の観測が `monoObs shHft mm` に等しく、(v) post を満たす任意の `raw` について `D'`（後処理済みの IR design。印刷後の design ではない。printer / SV 全体の保証とは別）上で `TopShips p n` が成り立つ。

**保証しないこと**:
1. **子の入口**。`synthesizeChild`（`sparkleChildSynth` が指す診断入口）は変えていない。子は `profile` を読み、ログを出し得る。文は子の入口を型に出さない（`hr` は上位 `Off` の run だけ）。子の合成中の IO（`IO.getEnv`・ログ・環境の変化）は `htop`/`hnoraw` の中の仮説であり、証明していない。Check18 `SCOPE` は、S1t/S1q/S1kStmt の接頭辞を持つ定数の値だけを辿る走査（コンパイラ本体も完全な依存閉包も辿らない）の範囲で、**文**（`HftFinalStmtOff`/`HftObTopCoreOff`/`HftObNoRawOff` の定義）が `synthesizeChild`/`sparkleChildSynth`/`childSynthEntry`/`synthesizeEntry`/診断入口を直接参照しないこと、**証明**が診断入口を直接参照しないこと、`synthesizeChild` が `synthesizeCombinational`（`Off` ではない）を呼ぶことを検査する。これは子の実行（child execution）が起きないことの検査ではない。注: 証明（`envFrame_coreHeadOff` と最終定理の値）は `CellPrem`（子の入口を保持する cell の状態の前提）を通じて `sparkleChildSynth` に触れる（`SCOPE-INFO` に列挙）。これは cell の内容についての**前提**であり、保証ではない。
2. **自動で非 leaf へ広げない**。4 leaf root の保証入口は `synthesizeCombinationalOff`（§21）。非 leaf の保証は上の仮説が全て供給されて初めて成り立つ条件付きの文であり、`synthesizeEntry`・旧 API・診断経路は旧入口のまま保証の外。`SPARKLE_PROFILE` 未設定で `else` 枝が選ばれたこと（§21.4）も供給していない。
3. `hcd`（`Ob`）・`hsrc`・`htop`・`hnoraw`・`hreadH/T`・`hchk`・`CellPrem`・`Laws/Start/hr` は**名前付き仮説のまま**（供給も縮約もしていない）。

### 24.3 組み立ての証明（`synth_hftPcieOutByte_finalOff`）

型: `∀ (CV : CDRel) (Ob : Environment → Prop), (∀ env, Ob env → HftObOf CV env) → HftFinalStmtOff Ob CV`。証明は S1k の `synth_hftPcieOutByte_final` と同じ形で、名前付き義務から結論を作る。インスタンス: `_Z`（`HftObCDZ`/`cdvZ`）、`_Y`、`_X`、`_old`（`fun _ => HftObCD`/`cdvOld`、旧 carrier の義務）、`_of`（`Ob := HftObOf CV`）。`hftFinalStmtOff_mono`（`CV ⊆ CV'` なら結論を移せる）。

**S1k の証明からそのまま持ち越せたもの**（carrier にも入口にも依らない）: `genGP_root_kids`（root の callee が全て leaf 行 ⇒ 表が `some p`、`p.decl`/`p.d`/`p.kD`）、kernel の事実（`root_wf/http_wf/tlp_wf`、`http_leaf/tlp_leaf`、`root_insts`、`root_kD`、`root_shape`）、`canon_row`、`startFacts_of_checked`、`EndpointLink` の組み立てと `observationsEqualMono_of_link`、`topShips_transport`、`hftRootType_shape`。

**入口の名前を替えた版が要ったもの**（S1q で作成済み。今回は使うだけ）: `postEntry` → `postEntryOff`、`root_find_of_headAt` → `root_find_of_headAtOff`、`machineDefinesLinked_of_reader_headAt` → `…_headAtOff`、`HeadAt` → `HeadAtOff`（`CellPrem` だけから）、`PostRun` → `PostRunOff`、`MachineDefinesLinked` → `…Off`。今回新たに書いたもの: `HftObTopCoreOff`/`HftObNoRawOff`（`Off` 版の義務）。

**CD 固有（旧 carrier）で新 carrier 版が要るもの**と、証明できたもの:
| 旧 | 新 | 状態 |
|---|---|---|
| `SourceDenotesMono`（`CD [] d.value`） | `SourceDenotesMonoV CV`（`CV env d.value`） | 定義。`cdvOld` で旧と `Iff.rfl` |
| `RootArtifactMono` | `RootArtifactMonoV CV` | 定義。`rootArtifactMonoV_mono`（`CV ⊆ CV'`）、`rootArtifactMono_to_Z` を証明 |
| `FGCircuitConclusionMono`/`fgCircuitConclusionMono_of_artifact` | `FGCircuitConclusionMonoV`/`fgCircuitConclusionMonoV_of_artifact` | 証明 |
| `DeclConnect`（`shapeOf` = domain binder 付きだけ） | `DeclConnectMonoV CV`（`monoShapeOf`）、`declConnectMonoV_of_rootArtifact`（root のみ）、`declConnectMonoV_mono` | 証明（callee は target にしない） |
| `sourceDenotesMono_unique`（`cd_fun`） | `sourceDenotesMonoV_unique`/`_eq`（`CDFunctional CV` が前提） | 証明。`cdvOld/X/Y/Z_functional` |
| `ObservationsEqualMono`（CD に依らない） | `observationsEqualMono_congr`、`observationsEqualMono_of_denotes` | 証明（意味の等式に沿って移る） |
| 4 leaf の `*_denotes`（`RootInEnv` + `CD` 導出 ⇒ `SourceDenotesMono`） | `sourceDenotesMonoV_mono cdvOld_to_Z` で移る | 証明（個別の新導出は不要） |
| `circCV` の `CDZ → CD` | 提供せず、使わない（非導出性の定理は無い） | 不在 |

### 24.4 関数性と、元ソースの値への導出の区別

- **関数性**（`CDFunctional`、`cdz_fun`、`sourceDenotesMonoV_unique`）: 同じ式・環境に対し、`CV` が導く型と値は**高々 1 つ**。これは関係が関数であるという性質で、証明済み（`cdvX/Y/Z/Old_functional`）。
- **元ソースの値への導出**: 導出 `CDZ env [] hftRootValue (MonoTy shHft) m` の索引 `m` を、元ソースの Lean 値 `synth_hftPcieOutByte` に**等しくする**ことは別の義務。`HftObCDZ` はこの導出そのもの（`m := synth_hftPcieOutByte` を索引に取る）で、**未供給**（S1r §22.4 の stuck: `bundle2`/`Signal.ap`、`Inhabited.mk`）。関数性があっても導出は得られず、導出があっても「規則の値が Lean 自身の定義である」ことは規則表の監査であり、`Expr` の書き換え（`recStep`/`MapStuck` 等）の意味保存は定理ではない（§22.3）。この束の文は、導出が**与えられたときに**結論へ接続する部分だけを証明する。

### 24.5 Check18 の出力

`kjob lake build Tools.ShippingFGCircuitS1tFinal`（exit 0）、`kjob lake build Tests.Gen5.FGCircuitPilotCheck18`（exit 0。土台の依存 919 jobs は冷たいビルド）。

- `FGCIRCUIT18 SIGNATURES`: `synth_hftPcieOutByte_finalOff`（全 carrier `CV`・全 `Ob` と橋 `hOb`）、インスタンス `_Z/_Y/_X/_old`、`cdvOld_to_Z`、`cdvZ_functional`、`sourceDenotesMonoV_unique`、定義 `SourceDenotesMonoV`/`RootArtifactMonoV`/`DeclConnectMonoV` の完全な型を独立に書いた文面（`ExpStmt`/`ExpThm`/…）と `isDefEq`（default）で照合し、binder の種類も一致。**60 mutant 棄却**（正規化後の式が構文的に異なり、かつ reducible 透過度で defeq でない）: `hr` が診断入口、コア義務が旧入口＋旧境界、旧 `PostRun`、旧 carrier の結論（`RootArtifactMono`）、reader / `hcd` / 結論が end world、各前提の欠落（`hcell`・`hchk`・`hreadH`・`hreadT`・`hcd`・`hsrc`・`htop`・`hnoraw`・`htop` 内の `hdRun`・橋 `hOb`）、別の root、別の post root、別宣言の data の `hchk`、carrier/義務の組の取り違え（`_Z` に `cdvY`/`cdvOld`/`HftObCDY`、`_old` に `cdvZ`、`_Y` と `_X` の入替）、`CD→CDZ` の逆向き、混在 carrier の関数性、形だけの一意性、定義から旧 carrier / params / levelParams / 形 / 観測 / post / `ShapeMatchesMono` を外したもの。`_Z` 文に対し 19 個の knob mutant も別に検査。
- `FGCIRCUIT18 HYPS`: 13 個の明示仮説 `L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hsrc htop hnoraw`（名前と順序を検査）。`hhead`/`hdRun`/`hquiet`/`hg`/`hio`/`hgates`/`hRead`/`hE` は仮説に無い。どの仮説の型（`S1t`/`S1kStmt` の定義を 1 段展開）にも診断入口・旧 `MachineDefinesLinked`・旧 `PostRun`・`coreHead`・`HeadIO`・`HeadAt`・`synthesizeChild` は現れない。定理の明示引数は `CV Ob hOb`。
- `FGCIRCUIT18 SCOPE`: 接頭辞 S1t/S1q/S1kStmt の走査の範囲で（コンパイラ本体・完全な依存閉包は辿らない。子の実行が起きないことの検査ではない）、文（17 定数）は診断入口・子の入口のどれも直接参照しない。証明（37 定数を走査）は診断入口を直接参照しない。走査は fuel 切れで todo が残れば throwError で失敗する。対照: S1k の最終定理は診断入口（`synthesizeCombinationalCore`、`PostRun`）を直接参照する。`synthesizeChild` は `synthesizeCombinational` を呼び `synthesizeCombinationalOff` を呼ばない。`synthesizeCombinationalOff` は `synthesizeChild`/`synthesizeEntry` に触れない。`SCOPE-INFO`: 子の cell（`sparkleChildSynth`）に触れる値は `envFrame_coreHeadOff` と `synth_hftPcieOutByte_finalOff`（`CellPrem` の前提経由）。
- `FGCIRCUIT18 LOWFUEL`: fuel 3 の走査（文・証明の 2 本）は失敗する（負の対照）。本番の走査は todo を残さず完了する。
- `FGCIRCUIT18 AXIOMS`: 28 名、標準 axiom のみ。`#print axioms` も同様（`propext`・`Classical.choice`・`Quot.sound`）。

### 24.6 証明したもの / 名前付き仮説・未供給 / 次

- **証明した**: `synth_hftPcieOutByte_finalOff`（と `_Z/_Y/_X/_old/_of`、`hftFinalStmtOff_mono`）、`cdvOld_to_X/X_to_Y/Y_to_Z/Old_to_Z`、`cdv*_functional`、`sourceDenotesMonoV_mono/unique/eq`、`observationsEqualMono_congr/of_denotes`、`rootArtifactMonoV_mono`、`rootArtifactMono_to_Z`、`fgCircuitConclusionMonoV_of_artifact`、`declConnectMonoV_of_rootArtifact/mono`。
- **名前付き仮説・未供給**: `hcd`（`HftObCDX/Y/Z` と S1s の family。導出が未供給）、`hsrc`（`ExtStage … 2` の帰納）、`htop`（machine 経路の `TopShips`、子の package/`ChildShips`/`ResetNk`、root の closing）、`hnoraw`（run から出す補題が無い）、`hreadH/hreadT`、`hchk`、`CellPrem`、`Laws/Start/hr`。子の入口 `synthesizeChild` の `profile` 固定は未実施（`initialize` の模型 `ShippingInitFrame`/`ShippingStartAtLoad` との対応を保つ設計が要る。§21.2）。
- 台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。条件付きは減算しない。
- **次**: (1) `hcd` の導出（S1s の DW family / `bundle2`・`Inhabited` の規則）。(2) `hsrc`（`ExtStage` 帰納）。(3) `htop`/`hnoraw`。(4) 子の入口の `profile` 固定（`HftObTopCoreOff` の中の子の IO を縮約するため）。

## 25. S1u（Issue `sparkle-fg-circuit-pilot` の次の束）: 非 leaf root `synth_hftPcieOutByte` の `hsrc` — `ExtStage` 帰納、子の `src`、残る root 側の 1 文

土台 `90d5ec10`（par/fgc-s1）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS1uSrc.lean`、`Tests/Gen5/FGCircuitPilotCheck19.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない。S1s の領域（`Tools/ShippingFGCircuitS1sCD.lean`、Check17、§23）には触れていない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で台帳に数えない。

### 25.1 手順 1: 文の固定（完全な型を先に）

`HftObSrc`（S1k §15.2、`Tools/ShippingFGCircuitS1kStmt.lean`）は**そのまま**（Check19 が S1k の文面と同じ独立文面 `ExpObSrc` と `isDefEq`）:
```
HftObSrc lvl env := ∀ p : Pkg ι (fun _ => defaultDomain), GPt lvl env hftRoot = some p →
  ∀ i bools bits, p.src i bools bits = monoObs shHft synth_hftPcieOutByte bools bits
```
`HftObSrc` を run 非依存の部分と子の事実に**分けた**。分割の全体の型（`Tools/ShippingFGCircuitS1uSrc.lean`）:

1. **子の `src`（証明した。仮説にしない）**: 子 `httpGetByte`/`tlpCplByte` は 2 つとも `ss = []`・`insts = []` の組合せ leaf（`genSemI` の `comb` 腕）。`genSemI_comb_src`: `gi.d = d`、`d.ss = []`、`d.shape.insts = []`、`machine_result` 型の式（任意の `x : HList (tys d.ss)` で成り立つ）から `(genSemI Q X gi).src = obs`。子の `obs` は宣言側の観測 `child.machineSource defaultDomain bools bits`（kernel の `Eq.refl` で出た生成済み endpoint の項: `fun t => ((httpGetByte (bits 1 6)).val t).toNat`、`tlpCplByte (bits 1 16) … (bits 6 5)`）。
2. **`ExtStage` 帰納（証明した）**: `callee` は package の `d`/`kD`/`src` しか読まない（`calleeOut`）。そこで `CalleeAgree q q' := q.d = q'.d ∧ q.kD = q'.kD ∧ q.src = q'.src`、`AgreeAt Q Q' c`、`TablesAgree Q Q' d`（`d` の callee 名の各点でだけ）を置き、`calleeOut_agree_tables` → `callOut_agree_tables` → **`ExtStage_agree_tables`**（段数 `n` についての帰納）→ `genSemGen_agree_tables`。有限リスト一般: callee 表が `d.shape.insts` の名前で `CalleeAgree` なら全段の `ExtStage` が一致する（HFT の `k = 2` は `d.shape.insts.length`）。
3. **表側（証明した）**: `genGP_root_kids_src`（S1k の `genGP_root_kids` の拡張）: root の callee が全て leaf 行なら、`genGP` の package の `src` は `genSemI (genS K) root (g.toIn hs)` の `src`、かつ各 callee 名 `c` で `genS K c = some (genSemI (genS K) c (gc.toIn hs))`（`genS_leaf_eq`）。
4. **root 側の 1 文（名前付き仮説 `HftRootLink`）**: 静的な 2 子の表 `hftKids`（`kidSem`: 子の `d`、`kDOf d`、`initsOf d`、`src := machineSource`）、完全な型:
```
HftRootLink : Prop := ∀ {ι : Type} (gi : GenIn), gi.d = synth_hftPcieOutByte.machineData →
  ∀ (i : ι) (bools : Nat → Signal defaultDomain Bool) (bits : (j n : Nat) → Signal defaultDomain (BitVec n)) (S : Signal defaultDomain (HList (tys gi.d.ss))),
    S.val 0 = gi.inits →
    (∀ t, S.val (t+1) = evalTerms (… typedVal gi.d.nIn … (extBOf hftKids gi i bools bits S) (extOf hftKids gi i bools bits S) t (S.val t) …) gi.d.nexts) →
    ∀ t, (monoObs shHft synth_hftPcieOutByte bools bits).map (fun f => f t) = gi.d.outs.map fun o => enc o.1 (eval … (extBOf hftKids gi i bools bits S) (extOf hftKids gi i bools bits S) … o.2)
```
`extBOf/extOf hftKids gi` = `ExtStage hftKids gi … gi.d.shape.insts.length`（root は callee 2 個）。run・環境・table に依存しない（root 宣言と子の宣言の観測だけの文）。`hftGenIn : GenIn`（`machine_ok`/`machine_body`/`initOk` の kernel 事実から）があるので量化は空でない。

組み立て `hftObSrc_of_rootLink : HftRootLink → ∀ {ι} lvl env, RootReader … root → RootReader … http → RootReader … tlp → HftObSrc lvl env`。証明: `canon_row` ×3、`genGP_root_kids_src`、`gi.d.ss` が空でない（kernel: `insts.isEmpty = false`）ので `genSemI` は `gen` 腕、`TablesAgree (genS K) hftKids gi.d`（子は `genSemI_comb_src` と `genSemI_d`/`genSemI_kD`）、`CalleesCausal (genS K) gi.d`（子は `comb` 腕: `genSemI_srcCausal`）、`ExtStage_agree_tables` で `genS K` から `hftKids` に移し、`genSemGen_src_eq_of_link`（下）と `HftRootLink`。

`genSemGen_src_eq_of_link`（一般、証明した）: `src_eq_of_states`（leaf: `ExtStage … 0 = id`）の非 leaf 版。loop の再帰は `loop_state_causal`（呼び出しの値は過去の状態にも依存するので pointwise でなく causal）、causal 性は `extCausal_of_genSem`（`CalleesCausal`）。仮定は「生成された再帰に従う任意の状態列について、宣言の観測 = データの `outs` の評価」（`hlink`）の 1 つ。

### 25.2 `synth_hftPcieOutByte_finalOffL`: `hsrc` を落とした最終文（`HftFinalStmtOffL Ob CV`）

`HftFinalStmtOff Ob CV`（S1t）から `hsrc` を除き、前に `(hlink : HftRootLink)` を置いたもの。`hsrc` は `hchk` と 2 つの子の reader から `hftObSrc_of_rootLink` で導く（`startFacts_of_checked` で root の reader を出す）。インスタンス `_Z/_Y/_X/_of`。**束縛の一覧（Check19 HYPS）**:

| | 明示仮説 |
|---|---|
| S1t `HftFinalStmtOff` | `L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd hsrc htop hnoraw`（13） |
| S1u `HftFinalStmtOffL` | `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hnoraw`（13） |

`hsrc`（`lvl`・環境・table に依存する文）が `hlink`（`HftRootLink`: run・環境非依存、root 宣言の 1 文）に**置き換わった**。仮説の個数は同じ（「1 つ減った」とは言わない）。変わったのは種類: 子の `src`・`ExtStage` 帰納・table 側の `genS`/`genGP` の扱いは仮説でなくなり、root 側の宣言の事実 1 文だけが残る。

### 25.3 何が残っているか（`HftRootLink`、FG D.D-3 / DG-SEM）と、なぜ閉じなかったか

`HftRootLink` は次の 2 つの事実を合わせたもの。どちらも root 固有で、この束では証明していない（impossible とは言わない）:
- **(a) 呼び出しの引数**: `ExtStage hftKids` の段 `k` は引数を `lsrcAt gi.d …`（データの `ls` 項の評価）から取る。一方 Lean 側の root は引数を Lean の Signal 式（レジスタの値）で渡す。`ls` の評価 = Lean の引数 Signal の値、という等式は root の生成済み endpoint に**無い**（`machine_writes`/`machine_result` は `nexts`/`outs` だけ、`machineExt` は `ls` を通らず Lean の呼び出しを直接使う。`machine_causal_k` は因果性だけ）。per-call の kernel 事実として生成するか、`ls` の項と Lean の引数式の対応を作る必要がある。
- **(b) fused 状態**: root は `Tele` で融合した状態（外側 `tys [bits 6]` と内側の `Sigs`）を持ち、endpoint の `machine_writes`/`machine_result` は `castSS (TeleT.fstate …)` 上の文。`GenIn` の `d.ss` 上の状態列 `S` を Lean 側の融合状態と同一視する帰納が要る（leaf root は `machineSigma` があるが、この root には `machineSigma` が無い）。

したがって前提の分類: 子の `src`・`ExtStage` 帰納・table 側（証明）/ `HftRootLink`（名前付き仮説）/ `hcd`（`Ob`）・`htop`・`hnoraw`・`hreadH/T`・`hchk`・`CellPrem`・`Laws/Start/hr`（S1t §24.2 のまま、供給していない）。S1s の領域（`hcd` の導出）は触れていない。

### 25.4 Check19 の出力

`kjob lake build Tools.ShippingFGCircuitS1uSrc`（exit 0、`#print axioms` は `propext`・`Classical.choice`・`Quot.sound` のみ）、`kjob lake build Tests.Gen5.FGCircuitPilotCheck19`（exit 0、922 jobs、error 0）。

- `FGCIRCUIT19 SIGNATURES`: `HftObSrc`（応用定義として）、`HftRootLink`、`hftObSrc_of_rootLink`、`ExtStage_agree_tables`、`genSemI_comb_src`、`synth_hftPcieOutByte_finalOffL` と `_Z` の完全な型を、独立に書いた文面（`ExpObSrc`/`ExpLink`/`ExpSrcThm`/`ExpStageAgree`/`ExpCombSrc`/`ExpFinalL`/`ExpThmL`）を正規化（定義の展開と literal Bool の `if` の選択）したものと `isDefEq`（default）で照合し、binder の種類も一致。**67 mutant 棄却**（正規化後の式が構文的に異なり、かつ reducible 透過度で defeq でない）: `HftRootLink` について 子の入れ替え（名前ごと／`src` だけ／`data` だけ）、http の `src` が tlp の観測、表が空、段数 `k = 0/1/3`、start 前提なし、再帰前提なし、結論が別の観測、別の root の `data`（12）。`HftObSrc` は観測なし／別の宣言（2）。`hftObSrc_of_rootLink` は link 欠落、root/http/tlp の reader の欠落、root の reader が別 data、結論が別宣言（6）。`ExtStage_agree_tables` は `d`/`kD`/`src` 一致の欠落（3）。`genSemI_comb_src` は `ss = []`/`insts = []`/観測式の欠落（3）。`synth_hftPcieOutByte_finalOffL`（全 carrier）は 20、`_Z` インスタンスは別 carrier（`cdvY`/`cdvOld`）・別 `Ob`（3）と、各 knob（link 欠落、**`hsrc` を残したもの**、診断入口の `hr`、旧 carrier の結論、`hcell`/`hchk`/`hreadH`/`hreadT`/`hcd`/`htop`/`hnoraw`/`htop` 内の `hdRun` の欠落、別の root、別の post root、別宣言の data の `hchk`、reader / `hcd` / 結論が end world）（18）。
- `FGCIRCUIT19 HYPS`: `synth_hftPcieOutByte_finalOffL_Z` の明示仮説は `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hnoraw`（13。名前と順序を検査）。`hsrc`・`hhead`・`hdRun`・`hquiet`・`hg`・`hio`・`hgates`・`hRead`・`hE`・`hP` は仮説に無い。どの仮説の型（`S1t`/`S1kStmt`/`S1u` の定義を 1 段展開）にも `HftObSrc`・診断入口・旧 `MachineDefinesLinked`・旧 `PostRun`・`coreHead`・`synthesizeChild`・`sorryAx` は現れない。`hlink` は run・環境・world・`MachineDefinesLinked` に触れない（run 非依存）。定理の明示引数は `CV Ob hOb`。
- `FGCIRCUIT19 AXIOMS`: 19 名、標準 axiom のみ。
- `FGCIRCUIT19 SNAPSHOT19`: 2 つの子の `machineSource` は宣言の観測（kernel `rfl`: `fun t => ((httpGetByte (bits 1 6)).val t).toNat`、`tlpCplByte (bits 1 16) … (bits 6 5)`）、`hftKids` は 2 つの子だけ（root 名では `none`）、`hftGenIn : GenIn` が root の data 上にある（量化は空でない）、root の `insts` は `[httpGetByte, tlpCplByte]`（段数 2）、root には `machineExt` があり `machineSigma` が無い（`HftRootLink` の (b) は endpoint の事実でない）。2 つの子には `machine_next`（組合せ leaf）。

### 25.5 次

(1) `HftRootLink` を (a) 呼び出し引数の対応（per-call の kernel 事実）と (b) fused 状態の同一視に分けて閉じる（(a) は `#machine_endpoint` 側の生成に近い）。(2) `htop`/`hnoraw`、`hcd`（S1s）。

## 26. S1x（Issue `sparkle-fg-circuit-pilot` の次の束）: `hnoraw : HftObNoRawOff` を run から供給する（`NoRawBelow` を全深さで）

土台 `15fb4615`（par/fgc-s1: S1v + S1u のマージ）。追加ファイル（既存は書き換えていない。lakefile 登録は各 1 回）: `Tools/ShippingFGCircuitS1xNoRaw.lean`、`Tests/Gen5/FGCircuitPilotCheck20.lean`。TRUSTED・axiom・sorry・native_decide・新しい law はない。S1s の領域（`Tools/ShippingFGCircuitS1sCD.lean`、Check17、§23）には触れていない。Issue の状態は変えていない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で台帳に数えない。

### 26.1 手順 1: 評価（先に記録する）

`HftObNoRawOff`（S1t）は、core run `(raw, D₀)` と後処理後（IR design、SV の印字ではない）`(b, D')` について (i) `∀ n, NoRawBelow D₀ raw.name (n+1) raw`、(ii) `∀ n, NoRawBelow D₀ raw.name (n+1) (checkedOptimize b)`、(iii) `b.body` のどの instance も `raw.name` を指さない、の 3 つ。`NoRawBelow` は「top に戻らない」ことで、グラフ全体の非循環は十分条件の 1 つにすぎず、要らない。`designTransport_of_noRawBelow` は全 `n` を要し、深さ 1..6 の snapshot は供給にならない。評価した結果:

1. **run が instance の target について与えるもの**: 子の module 名は子宣言から作られる（`synth c` が返す module の名前）が、**top と名前が違うことを名前の作り方（`ofDecl` の単射性）から出す道は取っていない**。代わりに、machine 経路の最後の `closeInsts`/`closeInstsG`（`Sparkle/IR/Machine.lean`、`MachineInstG.lean`）が **実行時に** 検査している: `noInstOfB m.name body && d'.modules.all (fun g => noInstOfB m.name g.body)`（「閉じる module の instance を、その module 自身と設計の全 module が持たない」）。結果 `(raw, D₀)` はこの検査を通った値なので、`raw` の body にも `D₀` の**全 module** にも `raw.name` を target にする instance は無い。既存の `closeInsts_acyclic`/`closeInstsG_acyclic`（`ShippingChildServe`）と `noRawBelow_of_noInstOf`（`ShippingGen5DCEntryS`、U-NORAW）がこれを `NoRawBelow`（全深さ）にしていたが、**core run とこの等式の接続**（S1x 以前の「Does NOT link a given core run's (raw, D)」）が無かった。
2. **`D'`（後処理済み）が top を自分の下に含み得るか**: `D' = topMap f raw D₀`（`PostEntry`）は名前が `raw.name` の module だけを差し替える。top 以外の module は `D₀` のままなので 1. の検査で自由。差し替えた top `b` は `dropZeroWidthModule raw` か、その `mergeChecked`。前者は instance 文の target を保つ（`dropZeroWidth_inst_target`: `dzStmt` は `.inst mn i conns` を `.inst mn i conns'` にするだけ）。後者は instance を含むなら `mergeChecked_inst`（`ShippingMachineShipsHier`）で `= dropZeroWidth raw`。よって `b` の instance の target は `raw` のそれに含まれ、`raw.name` ではない（`post_inst_target`、`noB_of_post`、(iii)）。`checkedOptimize b` は `hierGate b` の下で `b` と同じ instance 文を持つ（`checkedOptimize_inst_iff_gate`）。したがって `D'` は top を自分の下に含まない（`hgate` の下で）。
3. **最小の run-local な事実**: (a) 閉じる検査の結果 `NoInstOf raw.name raw.body ∧ ∀ g ∈ D₀.modules, NoInstOf raw.name g.body`（`coreOff_closed` で run から証明）、(b) 後処理後の top の文の gate `hierGate b = true`（`optimizeModule` が instance 文を保つ補題が木に無い枝（`checkedOptimize` の最後の `else o`）を避けるため。名前付きのまま）。

### 26.2 証明したもの（`Tools/ShippingFGCircuitS1xNoRaw.lean`、`kjob lake build` exit 0、標準 axiom のみ）

| 名前 | 内容 |
|---|---|
| `coreOff_closed` | `RunsTo (synthesizeCombinationalCoreOff X) … (m, d)`、`MachineDefinesLinkedOff … shape`、`MachineCloses … shape`、`shape.insts ≠ []` ⇒ `NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, NoInstOf m.name g.body`。`core_chainOff` → `synthesizeFromConst_machineR` → `synthesizeMachineCertified_returns`（`CloseCalls`）→ `closeInsts_acyclic`/`closeInstsG_acyclic`。法則 `Laws`・`JQ` は使わない |
| `coreOff_noRawBelow` | 上から `∀ k, NoRawBelow d m.name k m`（全深さ） |
| `dropZeroWidth_inst_target`、`post_inst_target`、`noB_of_post` | 後処理は instance の target を増やさない。(iii) |
| `noRawBelow_opt` | `hierGate b = true` の下で `∀ k, NoRawBelow D raw.name k (checkedOptimize b)`（(ii)） |
| `hftShape_insts_ne` | root の `shape.insts ≠ []`（S1u の kernel 事実から） |
| `hftObNoRawOff_of_run` | `hdRun`（core run の `MachineDefinesLinkedOff`）、`hcl : MachineCloses … hftRoot shape`、`hgate : HftPostGate …` ⇒ `HftObNoRawOff mctx mref cctx cref w b D'` |

`HftPostGate`（完全な型）: `∀ raw D₀ w1, RunsTo (synthesizeCombinationalCoreOff hftRoot) mctx mref cctx cref w (raw, D₀) w1 → PostEntry b raw D₀ D' → Sparkle.IR.RefineCheck.hierGate b = true`。

### 26.3 `hnoraw` を置き換えた最終文（束縛の一覧）

`HftFinalStmtOffLN Ob CV`（S1u の `HftFinalStmtOffL` の `hnoraw` を `hcl`・`hgate` に替えたもの）、`synth_hftPcieOutByte_finalOffLN`（全 `CV Ob hOb`）、インスタンス `_Z/_Y/_X`。**明示仮説（14）**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hcl hgate`（`hnoraw` は無い）。`hdRun`（core run の `MachineDefinesLinkedOff`）は S1t と同じく `hchk`/`hcell` から**内部で導く**（仮説にしない）。証明は `hftObNoRawOff_of_run hdRun hcl hgate` を `synth_hftPcieOutByte_finalOffL` の `hnoraw` に渡すだけ。

| | 明示仮説 |
|---|---|
| S1u `HftFinalStmtOffL` | `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hnoraw`（13） |
| S1x `HftFinalStmtOffLN` | `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hcl hgate`（14） |

仮説の数は 1 つ増えた（`hnoraw` が `hcl` と `hgate` の 2 つに分かれた）。変わったのは種類: `hnoraw`（`NoRawBelow` を全深さで）は、`hcl` と `hgate` から証明される形になった。**ただし `hcl : MachineCloses …` は `∀ tenv logProf w r w′` を量化する既存の強い未供給前提であり、これは対象 run だけから `hnoraw` を閉じたことではない**（対象 run 単独の事実は `RunsTo` と `MachineDefinesLinkedOff` までで、閉じる段が `none` を返さないことは全 world 前提のまま）。`hgate` も未供給。局所化は §28。

### 26.4 残っているもの（名前付き仮説。impossible とは言わない）

- **`hcl : MachineCloses … hftRoot synth_hftPcieOutByte.machineData.shape`**（FG D.T-4）: machine 経路の閉じる段が `none` を返さない。4 leaf root には生成済みの `machine_closes` がある（導出可能）が、この root には**無い**（Check19/Check20 SNAPSHOT が存在しないことを検査）。root は 2 つの call を持ち `closeInstsM/GM` を通る。`MachineCloses` は `closeInsts*` の `some` を要求するので、閉じる検査（`woCheck`・`linkedOk`・`kidsCombB` など）を子の実出力で評価する必要がある。S1iChild の `noRawBelowB` のような計算検査器で実出力を評価する道はあるが、run の結果に結ぶ部分は今回していない。
- **`hgate : HftPostGate`**（FG D.T-4）: 後処理後の top `b` が `hierGate` を満たす。`b` が `dropZeroWidth raw`（または merge）で、`raw.body` が instance と `seqStmtOk` な文だけなら成り立つはずだが、`raw` の body の形（closing が作る body）を run から導く補題は未作成。
- 子の合成中の IO（`synthesizeChild`・`sparkleChildSynth`）は `hr`/`htop` の中の仮説のまま（S1t §24.2）。`closeInstsGM` が使う `children` は `synth c`（診断入口）の結果だが、`coreOff_closed` は `CloseCalls` の存在量化だけを使い、子の run の内容には立ち入らない。

### 26.5 Check20 の出力

`kjob lake build Tools.ShippingFGCircuitS1xNoRaw`（exit 0）、`kjob lake build Tests.Gen5.FGCircuitPilotCheck20`（exit 0、923 jobs。作りを軽くした: 署名の照合を小さい `run_cmd` に分割。標準の `isDefEq`＋`whitelist` 展開の正規化）。

- `FGCIRCUIT20 SIGNATURES-A`: `HftPostGate`、`coreOff_closed` を独立に書いた文面（`GateTrue`/`ExpClosed`）と `isDefEq`（default）で照合し、binder の種類も一致。**8 mutant 棄却**（gate: 別の root／`hierBinds`／定数 true／`PostEntry` なし、closed: 閉じる前提なし／instance の前提なし／body だけの結論／旧 core の run）。
- `FGCIRCUIT20 SIGNATURES-B1`: `hftObNoRawOff_of_run`（`ExpRun`）に **6 mutant 棄却**（`hdRun` の shape が別、`hcl` の shape が別、`hcl` が別の宣言、`hdRun` が別の root、gate なし、定数 gate）。
- `FGCIRCUIT20 SIGNATURES-B2`: `synth_hftPcieOutByte_finalOffLN_Z` を独立に書いた `ExpFLN` と照合。**9 mutant 棄却**（`hcl` なし、別の shape、`hgate` なし、定数 gate、別 root の gate、carrier `cdvY`/`cdvOld`、obligation `HftObCDY`、`hnoraw` を残した S1u の文）。
- `FGCIRCUIT20 REMAINING`（2 行）: `hcl : MachineCloses … hftRoot synth_hftPcieOutByte.machineData.shape`、`hgate : HftPostGate …`。
- `FGCIRCUIT20 HYPS`: 14 個の明示仮説の名前と順序、`hnoraw`・`hsrc`・`hdRun` ほかは仮説に無い、`hcl` は `MachineCloses`、`hgate` は `HftPostGate`。仮説の「診断入口を直接参照しない」走査は、**仮説の型の定数と、`Tools.ShippingFGCircuitS1{t,kStmt,u,x}` の定義を 1 段だけ展開した定数**に対する限定的な走査であり、依存閉包全体に診断入口（`synthesizeChild` など）が現れないことの検査ではない。
- `FGCIRCUIT20 AXIOMS`: 12 名、標準 axiom のみ。
- `FGCIRCUIT20 SNAPSHOT20`: root は call 2 つ（kernel `decide`）、root に `machine_closes` は無く leaf root にはある。

Check の出力行は 8（SIGNATURES-A/B1/B2、REMAINING ×2、HYPS、AXIOMS、SNAPSHOT20）、棄却した mutant は計 23。

### 26.6 次

(1) `hcl`: 閉じる段の検査（`closeInstsG` の各 `Bool`）を、root の 2 つの子の実出力に対して評価し、`MachineCloses`（run の `none` を排除）にする。(2) `hgate`: 閉じた body の形から `hierGate`。(3) `htop`、`hcd`（S1s）、`HftRootLink`。

## 28. S1z（Issue `sparkle-fg-circuit-pilot` の次の束）: `hcl` を対象 run の閉じる成功へ局所化し、`hgate` を閉じた body の形から導く

土台 `a8a007e5`。追加ファイル: `Tools/ShippingFGCircuitS1zClose.lean`、`Tests/Gen5/FGCircuitPilotCheck23.lean`（lakefile 登録は各 1 回）。S1w2（`ShippingFGCircuitS1w*`、Check17/22、§23）と S1y（`ShippingFGCircuitS1yLink`、Check19/21、§25/§27）には触れていない。新しい law・axiom・TRUSTED・sorry・native_decide はない。Issue の状態は変えていない。成果は**条件付き**で台帳に数えない。

### 28.1 方針（先に型を決める。証明は 28.3 以降）

- **`hcl` の局所化**（レビュー裁定）。`MachineCloses`（`∀ tenv logProf w r w′`）を新たに全 world で仮定するのをやめる。仮定するのは**対象 `core_chainOff` が実際に通った経路の中の 1 回の machine run**（`synthesizeMachineCertified`）の閉じる成功だけ。その run は (a) 対象 core run `RunsTo (synthesizeCombinationalCoreOff declName) … w (raw, D₀) w1` の分解（`coreHeadOff`・`getConstInfo`・`getEnv`・`synthesizeFromConst` の run が結果 `(raw, D₀)` を返す）に紐づき、(b) `tenv` はその分解の `envR`、logger は `profLogIO false`、(c) 開始 world はその `synthesizeFromConst` が 2 回目に読む `getEnv` の終了 world `w8`（`w3` から読んだ `envR'`）、(d) shape は root の `machineData.shape`。この run の中で `closeInstsGM` が子の `synth c` を実行し、その**実出力**（`children`）に対して閉じる検査（`woCheck`/`linkedOk`/`kidsCombB` …）が評価される。別の子の出力ではない。
- **`hgate` の導出**。`HftPostGate` を仮説にせず、同じ局所化された閉じる成功から、`MachineRanA`（既存。その run が `some (raw, D₀)` を返し、`closeLets`、`CloseCalls`、`ChildrenRealA` を持つ）を作り、既存の `core_hierGate_anyA`（閉じた body は「instance + `closeMachine` の `seqStmtOk` 文」、後処理 `dropZeroWidth`／`mergeChecked` が文の種類を保つ）に渡す。snapshot は供給にしない。
- 仮説の個数: `hcl`＋`hgate`（14 個中の 2 つ）が **`hclL` の 1 つ**になる（明示仮説 13）。

### 28.2 完全な型

```lean
/-- 局所化した hcl: 対象 core run が通った machine run は `none` を返さない -/
def CoreCloses (declName : Name) (shape : MachineShape)
    (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State) (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State)
    (w : Void IO.RealWorld) : Prop :=
  ∀ (raw : Module) (D₀ : Design) (w1 : Void IO.RealWorld),
    RunsTo (synthesizeCombinationalCoreOff declName) mctx mref cctx cref w (raw, D₀) w1 →
    ∀ (s : CoreSaved) (wh w2 w3 w4 : Void IO.RealWorld) (envR : Environment) (ci : ConstantInfo),
      RunsTo (coreHeadOff declName) mctx mref cctx cref w s wh →
      RunsTo (getConstInfo declName) mctx mref cctx cref wh ci w2 →
      RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w2 envR w3 →
      RunsTo (synthesizeFromConst (fun e h t n => translateExprToWire envR e h t n) (profLogIO false) declName [] false true
        (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (instancePredicate envR))
        mctx mref cctx cref w3 (raw, D₀) w4 →
      ∀ (envR' : Environment) (w8 w10 : Void IO.RealWorld) (r : Option Res),
        RunsTo (Lean.getEnv : MetaM Environment) mctx mref cctx cref w3 envR' w8 →
        RunsTo (synthesizeMachineCertified (fun e hint top named => translateExprToWire envR e hint top named)
          (profLogIO false) declName shape) mctx mref cctx cref w8 r w10 →
        r ≠ none

abbrev HftCoreCloses mctx mref cctx cref w := CoreCloses hftRoot synth_hftPcieOutByte.machineData.shape mctx mref cctx cref w
```

`hgate` は仮説でなく定理: `hftPostGate_of_local`

```lean
theorem hftPostGate_of_local {mref cref} (L : Laws mref cref) {mctx cctx w b D'}
    (hstart : Start L mctx cctx w)
    (hdRun : ∀ raw D₀ w1, MachineDefinesLinkedOff mctx mref cctx cref hftRoot synth_hftPcieOutByte.machineData.shape w raw D₀ w1)
    (hclL : HftCoreCloses mctx mref cctx cref w) :
    HftPostGate mctx mref cctx cref w b D'
```

最終文（`hcl hgate` を `hclL` 1 つに替える）:

```lean
def HftFinalStmtOffLNL (Ob) (CV) : Prop :=
  ∀ (hlink : HftRootLink) {ι} {mref} {cref} (L : Laws mref cref) (lvl) (env₀) {mctx cctx w w' b D'}
    (hstart : Start L mctx cctx w)
    (hr : RunsTo (synthesizeCombinationalOff hftRoot) mctx mref cctx cref w (b, D') w')
    (hcell : CellPrem MkRefd mref cref) (hchk : CheckedStart …) (hreadH : …) (hreadT : …)
    (hcd : Ob (envAt cref w))
    (htop : ∀ p, GPt lvl (envAt cref w) hftRoot = some p → HftObTopCoreOff mctx mref cctx cref w b D' p)
    (hclL : HftCoreCloses mctx mref cctx cref w),
    (∃ raw, PostRunOff …) ∧ ∃ mm p, RootArtifactMonoV CV …
```

明示仮説（13）: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hclL`。

### 28.3 対照（Check23 が `isDefEq`＋独立に書いた文面で、次のそれぞれが**同じでない**ことを確認する）

- 別の world: `w8` の代わりに `w3`（getEnv を読む前の world）／`w`（対象 run の開始 world）で machine run を始める。
- 別の shape: root の shape の代わりに `counterLoop` の shape／`httpGetByte` の shape。
- 別の出力: 結論が `r ≠ none` でなく `r = none`／`r = some (raw, D₀)`（強すぎる）／`r ≠ some (raw, D₀)`。
- 別の run: 対象 core run に紐づかない（`RunsTo core … (raw, D₀) w1` の前提なし）、分解を fresh な `tenv logProf` で量化した旧 `MachineCloses` の形。

### 28.4 証明したもの（`Tools/ShippingFGCircuitS1zClose.lean`、`kjob lake build` exit 0、標準 axiom のみ）

| 名前 | 内容 |
|---|---|
| `CoreCloses`、`HftCoreCloses` | 28.2 の型（局所化した `hcl`） |
| `coreCloses_of_machineCloses` | 全 world の `MachineCloses` ⇒ `CoreCloses`（局所化は**弱い**前提。強い前提を新たに足したのではない） |
| `synthesizeFromConst_machine_invW` | 既存 `…_invR` の写し。machine run の**開始 world を露出**（本体の `getEnv` が読む `w6`）。証明は `invR` と同じ |
| `coreOff_ranA` | `Start L`、core run、`MachineDefinesLinkedOff`、`CoreCloses` ⇒ `MachineRanA L.O …`（run が `some (raw, D₀)`、`closeLets`、`CloseCalls`、`ChildrenRealA`）。`core_chainOff` → `coreHeadOff_jqcA`/framed で `JQC (0+1)` を `w3` まで運び、`invW` で `w8` へ、`CoreCloses` で `r ≠ none` |
| `closed_of_ranA` | `MachineRanA` ⇒ `NoInstOf m.name m.body ∧ ∀ g ∈ d.modules, …`（`closeInsts_acyclic`/`closeInstsG_acyclic`） |
| `hft_callsOk`、`hft_slots`、`hft_domB`、`hft_outTy`、`hft_nomem` | root の `machineData` の事実（kernel `decide`） |
| `hftPostGate_of_local` | **`hgate` の導出**: `coreOff_ranA` ＋ 既存 `core_hierGate_anyA`（閉じた body ＝ instance ＋ `closeMachine` の `seqStmtOk` 文、後処理の 2 枝）。`HftPostGate` は仮説でなくなった |
| `hftObNoRawOff_of_local` | `HftObNoRawOff` を `Start L`・`hdRun`・`HftCoreCloses` から |
| `HftFinalStmtOffLNL`、`synth_hftPcieOutByte_finalOffLNL`（`_Z/_Y/_X`） | 28.2 の最終文。**明示仮説 13**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hclL`（S1x の 14 から `hcl hgate` が `hclL` 1 つに） |

`hdRun` は S1x と同じく `hchk`/`hcell` から内部で導く。

### 28.5 残るもの（名前付き仮説。impossible とは言わない）

- **`hclL : HftCoreCloses`**（FG D.T-4）。対象 run が通った `synthesizeMachineCertified` が `none` を返さない: `closeLets` が root の transition を受理し、`closeInstsGM` の閉じる検査（`woCheck`・`linkedOk`・`kidsCombB` など）が**同じ run の中で実行された子の実出力**（`synth c`）に対して成り立つ。ここでは証明していない。対象 core run の結果 `(raw, D₀)` だけでは、machine 経路が `none` を返して fallback 経路が同じ型の `(Module × Design)` を返した場合を除外できない（`synthesizeFromConst` の定義）。証明には子の run の実出力（`hr`/`htop` の内側の IO、§24.2）に対する検査の評価が要る。
- 他の仮説（`HftRootLink`、`hcd`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws`/`Start`/`hr`）は S1x のまま。`hgate` と `hnoraw` は仮説から消えた。
- 仮説走査（Check23 HYPS）は S1w2/S1y と同じ限定走査（型の定数と、パイロットの定義の 1 段展開）。依存閉包全体に診断入口が現れないことの検査ではない。

### 28.6 Check23 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck23`、exit 0、924 jobs）

- `FGCIRCUIT23 SIGNATURES-A`: `HftCoreCloses` を独立に書いた `ExpCC`（world・env・logger・shape・出力・root を引数にしたもの）と `isDefEq`（default）で照合。**14 mutant 棄却**（別 world: `w3`／開始 world `w`、別 shape: `counterLoop`／`httpGetByte`、別出力: `= none`／`= some (raw, D₀)`／`≠ some (raw, D₀)`／`True`、別 env、別 logger、別 root、全 world の `MachineCloses`、core run なし、`synthesizeFromConst` との連結なし）。
- `FGCIRCUIT23 SIGNATURES-B`: `hftPostGate_of_local`・`hftObNoRawOff_of_local` を照合。**13 mutant 棄却**。
- `FGCIRCUIT23 SIGNATURES-C`: `synth_hftPcieOutByte_finalOffLNL_Z` を `ExpFLNL` と照合。**12 mutant 棄却**（`hcl`＋`hgate` を残した S1x の文を含む）。
- `FGCIRCUIT23 REMAINING`（1 行）: `hclL`。`FGCIRCUIT23 HYPS`: 13 個の名前と順序、`hnoraw`/`hcl`/`hgate`/`hdRun` ほかは仮説に無い、限定走査の注記つき。
- `FGCIRCUIT23 AXIOMS`: 15 名、標準 axiom のみ。

Check の出力行は 6、棄却した mutant は計 39。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き（`hclL` ほか）。

### 28.7 次

(1) `hclL`: root の 2 つの子（`httpGetByte`、`tlpCplByte`）の実出力に対し、`closeInstsGM` の検査を評価する計算検査器（S1iChild の `noRawBelowB` の型）を run の結果に結ぶ。(2) `htop`、`hcd`（S1s／S1w2）、`HftRootLink`（S1y）。

## 29. S2a（Issue `sparkle-fg-circuit-pilot` の次の束）: `hclL` — 対象 run の閉じる成功を、根のデータと子の実出力から供給する

土台 `451e3467`（par/fgc-s1）。追加ファイル: `Tools/ShippingFGCircuitS2aClose.lean`、`Tests/Gen5/FGCircuitPilotCheck24.lean`（lakefile 登録は各 1 回）。S1w2（`ShippingFGCircuitS1w*`、Check17/22、§23）と S1y（`ShippingFGCircuitS1yLink`、Check19/21、§25/§27）、S1z のファイルには触れていない（S1z の定義・定理を import して使う）。新しい law・axiom・TRUSTED・sorry・native_decide はない。snapshot は供給にしていない。Issue の状態は変えていない。成果は**条件付き**で台帳に数えない。

### 29.1 手順 1: `some`/`none` を決める Bool 検査（完全な型）

`synthesizeMachineCertified translate logProf declName shape : MetaM (Option (Module × Design))`（`Sparkle/Compiler/Elab.lean`）は、`synthesizeMixedCertified` の結果 `(t, design)` に対し:

1. `Sparkle.IR.Machine.closeLets (nLets : Nat) (t : Module) : Option Module`。`nLets = 0` なら `some t`。それ以外は `packedWire? t.body`、`letOperands` が通り、かつ `aliases.all (wireWidth t.wires pa.2 == pa.1.ty.bitWidth && 0 < pa.1.ty.bitWidth && pa.1.name != "out" && pa.2 != "out" && !(writesOf t.body).contains pa.1.name) && core != "out" && OptCheck.assignmentOrderCheck body'`。`none` なら run は `none`（fallback）。
2. `shape.insts = []` なら `some (closeMachine …)`（検査なし）。`insts ≠ []` かつ `shape.instFields.isEmpty` なら `closeInstsM` → **`closeInsts`**、`instFields ≠ []` なら `closeInstsGM` → `closeInstsG`。**根 `synth_hftPcieOutByte` は `instFields = []` なので `closeInsts` の道**（kernel `decide`、`Check24`/ビルドで確認）。
3. `closeInstsM` は `sparkleChildSynth.get` で子の `synth c`（MetaM、子ごとの実行）を走らせ `children : List (Module × Design)` を得て `closeInsts nIn kI n portNames insts children (m, d)` を評価する。`closeInsts : Option (Module × Design)` が `none` になる条件: (a) `instStmt` の各検査（`mc ← moduleByName d'.modules child.1.name`、引数数・ポート名・出力の重複 …）、(b) `topoBody m'.body` が `none`、(c) `stmts.all isInst && decide portNames.Nodup && woCheck [] m'.body && woCheck [] body && isPermOf m'.body body && decide (seqOf m'.body = seqOf body) && decide (nextKeys m'.body).Nodup && decide (m'.body.filterMap stmtMemName).Nodup && linkedOk (moduleByName d'.modules) body && children.all (fun c => decide (moduleByName d'.modules c.1.name = some c.1) && c.2.modules.all (…)) && noInstOfB m.name body && d'.modules.all (fun g => noInstOfB m.name g.body) && kidsCombB d'.modules body`。
4. 子に依存するのは (a) と (c) の `linkedOk`、`children.all …`、`noInstOfB`、`kidsCombB`（子の module の形: `isAssign` だけ、入力から読む、出力が書かれる、入力が wire で接続される）。根だけに依存するのは `closeLets` と `topoBody`/`woCheck` 系の根の body の部分。

### 29.2 手順 2/3: 何を、どこまで証明したか

方針: 既存の `machineClosesAtA_of_gateKids'`（`ShippingCallsGatePinned`、cache pin 版。`closeLets` は `letsClose_of_data`、`closeInsts` は `callsPureP_of_gateKids`）を、根の `machineData` と**子の実出力**（`RealChildA`）に対して使う。子の側の前提 `RealChildA O c y → ChildIface c n y.1 y.2`（`ChildComb`、入力数、module 名 = `ofDecl c`、design の module が空）を、`RealChildA.run` が運ぶ**子自身の run**（`synthesizeCombinational c` が `(y.1, y.2)` を返す）から導く。

| 名前 | 内容 |
|---|---|
| `machineChild_ifaceA` | `machineChild_iface`（`ShippingMachineChildRun`）の `RealChildA` 境界への移植。機械 run は `machine_run_of_coreA`、閉じは `synthesizeMachineCertified_runsA`（`BodyStepC O`、`htr_of_tele`）。以降の証明は旧版そのまま |
| `machineChild_of_realA` | `RealChildA O c y` ⇒ `ChildIface c (…) y.1 y.2`（slotless な machine 子）。`RealChildA` の `adm/cache/synth/quiet/hr` から `JQC O (dv w) w` を作り、`MachineDefines.ctx` で反射を子の文脈に移す |
| `hft_kid_iface` | 根の 2 つの子（`httpGetByte`、`tlpCplByte`）の実出力に `ChildIface c (nkOf c)`。子のデータ検査（`ok`、`machine_body`、`gateCallsOk`、`lets ≠ 0`、`insts = []`、`slots = []`、出力が `out` 1 つ、`outTy`）は kernel `decide`。子の `MachineCloses` は生成済み `X.machine_closes` |
| `hft_gateCalls`、`hft_alias`、`hft_argsN`、`hft_kids_names`、`hft_noparent`、`hft_outs_head` | 根のデータの事実（kernel `decide +kernel`）: `gateCallsOk (kDOf …)`、`letsAliasOk`、呼び出しの引数数、呼び出し先が 2 つの子のどちらか、親の名前の呼び出しが無い、出力ポート名が `i` で始まらない |
| `hft_closesAtA` | 根の `MachineClosesAtA`（任意の `JQC O n` world（`1 ≤ n`）から機械 run は `none` を返さない）。`machineClosesAtA_of_gateKids'` ＋ 上の事実。`names_inj`/`parent_ne`/`instName_ne_of_head` は既存 |
| `hftCoreCloses_of_kids` | **`HftCoreCloses`（hclL）の導出**: `Start L mctx cctx w` と `HftKidsDefine` から。`JQC (0+1)` を core の連鎖（`coreHeadOff_jqcA`、`FramedA.constInfo/env`）で `w3`、`getEnv` の frame で `w8` へ運び（`coreOff_ranA` と同じ道）、`hft_closesAtA` を `w8` の機械 run に適用 |
| `HftFinalStmtOffLNK`、`synth_hftPcieOutByte_finalOffLNK`（`_Z/_Y/_X`） | S1z の最終文の `hclL` を `hkids : HftKidsDefine …` に替えたもの。**明示仮説 13**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hkids`（`hclL` は仮説でなくなった） |

標準 axiom のみ（`#print axioms` と Check24 AXIOMS）。`hdRun`（根の `MachineDefinesLinkedOff`）は `hftCoreCloses_of_kids` には要らない（根の閉じる成功は shape の反射ではなく `JQC` と子の事実から出る）。

### 29.3 残る名前付き仮説（impossible とは言わない）

```lean
/-- 2 つの被呼び出し宣言の反射（FG D.T-4、子の部分）。生成済み endpoint が各被呼び出し宣言について既に取っている `MachineDefines` の前提そのもの -/
def HftKidsDefine (mctx : Meta.Context) (mref : ST.Ref IO.RealWorld Meta.State)
    (cctx : Core.Context) (cref : ST.Ref IO.RealWorld Core.State) : Prop :=
  MachineDefines mctx mref cctx cref ``Sparkle.IP.Net.HTTP.httpGetByte Sparkle.IP.Net.HTTP.httpGetByte.machineData.shape ∧
  MachineDefines mctx mref cctx cref ``Sparkle.IP.Bus.PCIe.tlpCplByte Sparkle.IP.Bus.PCIe.tlpCplByte.machineData.shape
```

- `MachineDefines` は「その run の環境で `getConstInfo c` / `getEnv` を読んだとき、`entryConst` が証明済みの shape を与える」ことの全 world 版（`ShippingMachineEntry`）。**閉じる成功そのものではない**（`hclL` の「`none` を返さない」は上で導出済み）。根では同じ種類の事実を `CheckedStart`/`hcell` から run 局所の `MachineDefinesLinkedOff` に落としていた（S1q）。子では、子の run は `RealChildA` の任意の admissible world で走るため、環境セルが子の run の world でも同じことを `JQC` は言わない。子の反射を `hreadH`/`hreadT`（`RootReader`）と `CellPrem` から子の run の world へ運ぶには、子の run の world の環境セルが開始 world と等しいことが要る（`RealChildA` は深さと cache しか持たない）。これは次の一歩（29.5）。
- 他の仮説（`HftRootLink`、`hcd`、`htop`、`hreadH/T`、`hchk`、`CellPrem`、`Laws`/`Start`/`hr`）は S1z のまま。

### 29.4 Check24 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck24`、exit 0、931 jobs）

- `FGCIRCUIT24 SIGNATURES-A`: `HftKidsDefine` を独立に書いた `ExpKD`（2 つの (宣言名, shape)）と `isDefEq` で照合。**8 mutant 棄却**（名前の入れ替え、両方 `httpGetByte`、両方 `tlpCplByte`、別 shape（`counterLoop`）、根の shape、別の子、片方だけ、`True`）。
- `FGCIRCUIT24 SIGNATURES-B`: `hftCoreCloses_of_kids` の束縛（`mctx mref cctx cref L w hstart hk`）と使う定数（`Start`、`HftKidsDefine`、`HftCoreCloses`；`MachineCloses`/`MachineClosesAtA`/`CoreCloses` を前提に持たない）、`synth_hftPcieOutByte_finalOffLNK_Z` の 13 仮説・`hkids` が最後・`hclL` が無い・S1z の文と違う。**5 構造検査**。
- `FGCIRCUIT24 HYPS`（13 個）、`FGCIRCUIT24 CONTROLS`（小さな module 上の純粋検査 14 件を kernel で判定、ビルドが失敗すれば反転）: 組合せ的な子は `kidsCombB` を通る／順序回路の子・入力が配線されていない子・出力が書かれない子（別の子出力）・子が無いは落ちる／親の instance は `noInstOfB` で落ちる／`closeLets` は packed wire の無い module を拒否／根の `gateCallsOk` は本来の `nDecl` で成立し別の `nDecl` で不成立／別の引数数の読みは不成立。
- `FGCIRCUIT24 REMAINING`（1 行）: `hkids`。`FGCIRCUIT24 AXIOMS`: 15 名、標準 axiom のみ。

- `FGCIRCUIT24 SIGNATURES-C`（S2e で追加）: `hftCoreCloses_of_kids` と共通の最終文 `synth_hftPcieOutByte_finalOffLNK_Z` の**完全な型**を、独立に書いた期待型（`ExpCore`、`ExpFinalK`；world/ref/context、entry、carrier/obligation、出力、結論まで）と `isDefEq`（binder kind も）で照合。実型の正規形は 1 回だけ計算して使い回す（Check19 と同じ）。束縛名を維持したまま棄却した mutant: `hftCoreCloses_of_kids` 15（別の子・入れ替え・片方だけ・`True`、前提の欠落（Start／hk）、結論の欠落、別 root、別 shape、別 world、Start の world、別 context（Meta/Core）、別 ref（Meta/Core））、最終文 25（別 carrier／別 obligation／旧 carrier、旧 entry（診断版）、旧 artifact、前提 hcd／htop／hkids の欠落、別の子仮説 4 種、別 root／post root、別出力、hcd／結論を終了 world に、別 ref／context（各 2）、別 design、結論の片方または両方の欠落）。これで「最後の仮説だけ違う」ことを型全体で機械的に示す（SIGNATURES-B の構造検査は補助）。
- 注: 上の SIGNATURES-A の `HftKidsDefine` docstring の「run-local」は contexts（と ref セル）が固定という意味だけで、world は全称（子の run の world を含む全 world 前提）。

Check の出力行は 7、棄却した mutant は 8（SIGNATURES-A）＋15＋25（SIGNATURES-C）、制御は 14（CONTROLS）＋構造検査 5。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き（`hkids` ほか）。

### 29.5 次

(1) `HftKidsDefine`: 子の run の world でも環境セルが開始 world と同じであること（`RealChildA` に環境の frame を足すのではなく、`Start` からの run 局所の連鎖で `getConstInfo c`/`getEnv` の読みを `hreadH`/`hreadT` に結ぶ）。(2) `htop`、`hcd`（S1s／S1w2）、`HftRootLink`（S1y）。

### 29.6 ビルド環境の注記

`ulimit -v 20000000 … kjob lake build` は、この Pod では大きな既存モジュールのビルドで `failed to create thread`（Lean が確保する仮想メモリ）になるため、`timeout 1500 kjob lake build TARGET` のみで実行した。メモリの上限は kjob 側（`-m`）に任せた。

## 32. S2d（Issue `sparkle-fg-circuit-pilot` の次の束）: `hkids` の run 局所化 — 子の run の開始 world の環境の 2 つの事実

土台 `b7984ea2`（par/fgc-s1）。追加ファイル: `Tools/ShippingFGCircuitS2dKids.lean`、`Tests/Gen5/FGCircuitPilotCheck26.lean`（lakefile 登録は各 1 回）。S2a（§29）・S2b・S2c のファイルには触れていない（S2a の定義・定理を import して使う）。新しい law・axiom・TRUSTED・sorry・native_decide はない。Issue の状態は変えていない。成果は**条件付き**で台帳に数えない。

### 32.1 何が `HftKidsDefine` の代わりに要るか（完全な型を先に）

`HftKidsDefine`（§29.3）は 2 つの被呼び出し宣言の `MachineDefines`（全 world、子の run の `mctx cctx` で）。子の run は `RealChildA.run` の `adm/cache/synth/quiet/hr`（深さと cache だけ）で任意の admissible world で走り、環境セル `envAt cref w` は持たない。根では `CheckedStart`（`ReadsAt env₀ cref w`）と `HeadAt`/`GetEnvProfileAt` で `MachineDefinesLinkedOff` を run 局所に作った（S1q）。子も同じ形で作れるが、**子の run の開始 world の環境が開始 world のそれと一致すること**は `Laws` からも `CellPrem` からも導けない（`quiet` は不透明、class-D の `whnf`/`inferType` 等は env frame を持たない、§21）。最小の run 局所の事実として次の 2 つに分けて名前を付けた（各 `RealChildA.run` が運ぶ前件のもとで、その子の full-entry run の開始 world `w` について）。

```lean
/-- NAMED HYPOTHESIS (FG D.T-4k) -/
def KidStartEnv (O : RefLawsAOps MkRefd mref cref) (e : Environment) (c : Name) : Prop :=
  ∀ (mctx' : Meta.Context) (cctx' : Core.Context) (w w' : Void IO.RealWorld) (y : Res),
    AdmCtx O.quiet mctx' cctx' → (∀ c' r', (cv w).get? c' = some r' → RealChildA O c' r') →
    sv w = some synthesizeChild → O.quiet w →
    RunsTo (synthesizeCombinational c) mctx' mref cctx' cref w y w' →
    ReadsAt e cref w ∧ GetEnvProfileAt mctx' mref cctx' cref w

def HftKidsStartEnv O e := KidStartEnv O e hftHttp ∧ KidStartEnv O e hftTlp     -- FG D.T-4k
def HftKidsGates e := EntryGates e hftHttp ∧ EntryGates e hftTlp                 -- FG D.T-4g
```

- (A) `ReadsAt e cref w`: 子の開始 world の Core 環境は `e = envAt cref w₀`（開始 world）と一致（find の包含と `instancePredicate/userInliner/structEnv` の等式）。根から子までの world の連鎖の環境 frame の事実。
- (B) `GetEnvProfileAt mctx' … w`: 子の `synthesizeChild` → `synthesizeCombinational` が `coreHead` で読む `IO.getEnv "SPARKLE_PROFILE"` は `none` を返し環境を変えない（根の S1o と同じ profile 無効の枝。診断入口は取らない）。
- `HftKidsGates e`: 2 つの被呼び出し宣言の entry 定数の 2 つの拒否（`certifiedShape?`/`mixedCertifiedShape?` = `none`）。根の `hchk` の gate 部に当たる。`machineShape?` の部分は既存の `hreadH`/`hreadT`（`RootReader`）がそのまま運ぶ。
- 全 world の `MachineDefines` は消え、`HftKidsStartEnv`/`HftKidsGates` から `MachineDefines`/`HftKidsDefine`/`MachineCloses` は到達不能（Check26 SIGNATURES-B）。`KidStartEnv` は shape も閉じる成功も言わない。

### 32.2 証明したこと

| 名前 | 内容 |
|---|---|
| `machineChild_ifaceK` | `machineChild_ifaceA` の `entry : MachineDefines` を「この子の core run の開始 world `w` だけに対する `MachineDefinesLinked`」に替えたもの。機械 run は `machine_run_of_coreC`（run 自身の `core_chain`）。それ以外の証明は `machineChild_ifaceA` と同一（コピー） |
| `machineDefinesLinked_of_readerE` | `ReadsAt e cref w`、`HeadAt X w`、`GetEnvFrame`、`RootReader lvl e X dd`、`EntryGates e X` から `MachineDefinesLinked … X dd.shape w M D w'`。`machineDefinesLinked_of_headAt` と同じ証明だが、定数の lookup は run 自身の `getConstInfo`（`ci_of_readsAt`）から取り、`RootInEnv` を要さない |
| `machineChild_of_realK` | `machineChild_of_realA` の `entry` を `KidStartEnv` ＋ reader ＋ gates ＋ `CellPrem` に替えたもの。`HeadAt` は `headAt_of_profileOff`（`CellPrem` ＋ (B)）、`GetEnvFrame` は `getEnvFrame_of_cellPrem` |
| `hft_kid_ifaceK`、`hft_closesAtK`、`hftCoreCloses_of_kidsK` | S2a の `hft_kid_iface`、`hft_closesAtA`、`hftCoreCloses_of_kids` の `hk : HftKidsDefine` を `hcell hrH hrT hg hke` に替えたもの |
| `HftFinalStmtOffLNKK`、`synth_hftPcieOutByte_finalOffLNKK`（`_Z/_Y/_X`） | S2a の最終文の `hkids` を `hkenv : HftKidsStartEnv L.O (envAt cref w)`、`hkgates : HftKidsGates (envAt cref w)` に替えたもの |

**binder 一覧（`finalOffLNKK_Z`、明示仮説 14）**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hkenv hkgates`（S2a は 13 個で最後が `hkids`）。`hcell`（`CellPrem`）、`hreadH`/`hreadT` は既存の仮説で、子のために新しく足したのは `hkenv`（D.T-4k）と `hkgates`（D.T-4g）だけ。標準 axiom のみ（`#print axioms` と Check26 AXIOMS）。

### 32.3 残る名前付き仮説（impossible とは言わない）

`hkenv`（FG D.T-4k: 子の開始 world の環境の `ReadsAt` と profile 無効）、`hkgates`（FG D.T-4g: 子の entry 定数の gate 2 つ、環境 `envAt cref w` 上の計算）、および S2a から変わらない `HftRootLink`（S2c）、`hcd`（S2b）、`htop`、`hreadH`/`hreadT`、`hchk`、`CellPrem`、`Laws`/`Start`/`hr`。`hkgates` は `entryGatesB` と同種の評価検査（MetaM）で、kernel では計算していない。`hkenv` の (A) は `QuietStrength`（強めた `L'`）の構成が `diag` と `RefLawsATele` の `telescope` を含まないため `Laws` から導いていない（`frameQ_plus` 等は class-D 行を除く、S1i）。(A) を `RealChildA` の world の連鎖から導くには、根の機械 run 全体の環境 frame（class-D の `whnf` 等を含む）が要る。

### 32.4 Check26 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck26`、exit 0、932 jobs）

- `FGCIRCUIT26 SIGNATURES-A`: `KidStartEnv` を独立に書いた `ExpKS` と `isDefEq` で照合。**8 mutant 棄却**（ReadsAt のみ、profile のみ、ReadsAt を終了 world で、profile を終了 world で、`ReadsAt` の代わりに環境等式、cache 前件を落とす、profile 無効入口 `synthesizeCombinationalOff`、`True`）。
- `FGCIRCUIT26 SIGNATURES-B`: `hftCoreCloses_of_kidsK` の binder と使う定数、`finalOffLNKK_Z` の 14 仮説（`hkids`/`hclL` が無い、`hkenv`/`hkgates` が最後、`MachineDefines`/`HftKidsDefine`/`MachineCloses` が新仮説から到達不能、S2a の文と違う）。**8 構造検査**。`FGCIRCUIT26 HYPS`（14 個）。
- `FGCIRCUIT26 CONTROLS`: kernel 判定 6 件（`hftHttp`/`hftTlp` が 2 つの被呼び出し宣言、互いに異なり根とも異なる、入れ替えは不成立）。
- `FGCIRCUIT26 REMAINING`（2 行: `hkenv`、`hkgates`）。`FGCIRCUIT26 AXIOMS`: 10 名、標準 axiom のみ。

Check の出力行は 8（SIGNATURES-A 1、SIGNATURES-B 1、HYPS 1、CONTROLS 1、REMAINING 2、AXIOMS 1 + 構造検査 8 / mutant 8 / 制御 6）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き。

### 32.5 次

(1) `hkgates`: 2 つの被呼び出し宣言の gate 検査（`entryGatesB` 相当）を `envAt cref w` 上で評価する Check（FG D.T-4g）。(2) `hkenv` (A): `RealChildA` の開始 world の環境が根の開始 world のそれと一致すること（機械 run の class-D 行の環境 frame、または run 局所の world の連鎖）、(B): 子の `synthesizeCombinational` の profile lookup が `none`。(3) `htop`、`hcd`（S2b）、`HftRootLink`（S2c）。

### 32.6 ビルド環境の注記

`timeout 1500 kjob lake build TARGET` のみ（`ulimit -v` なし）。`Tools.ShippingFGCircuitS2dKids` は約 3 分（初回、S2a の import 込み）。

## 33. S2g（Issue `sparkle-fg-circuit-pilot` の次の束）: `hkgates` — 2 つの被呼び出し宣言の gate を閉じた宣言と有限個の環境問い合わせに還元

土台 `6bfe8328`（par/fgc-s1）。追加ファイル（既存の定理は書き換えていない。lakefile 登録 2 件）: `Tools/ShippingFGCircuitS2gGates.lean`、`Tests/Gen5/FGCircuitPilotCheck27.lean`。sorry・axiom・native_decide・TRUSTED・新しい law はない。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は引き続き**条件付き**で、approved/done ではない。

### 33.1 完全な型（先に固定。Check27 が独立に書いた文面と `isDefEq`）

```
structure KidGateFacts (env : Environment) (X : Name) (T V Vi : Lean.Expr) : Prop where
  root   : ∃ d : DefinitionVal, RootInEnv env X T V d
  ui_val : userInliner env V = Vi
  ui_ty  : userInliner env T = T
  ip_val : instancePredicate env (peeled V) = false
  ip_inl : instancePredicate env (peeled Vi) = false

def HftKidsGateFacts (e : Environment) : Prop :=
  KidGateFacts e hftHttp httpType httpValue httpInlValue ∧ KidGateFacts e hftTlp tlpType tlpValue tlpInlValue
```

`T`/`V` は被呼び出し宣言（`httpGetByte`、`tlpCplByte`）の型/値の**閉じた `Lean.Expr` の quote**（`quote_decl%`、`exprToE`）、`Vi` は `userInliner env V` の quote（`arbiterInlinedValue` と同じ、この build の環境の **SNAPSHOT**。それが環境の inliner の返す値であるという事実は名前付き仮説 `ui_val`）。`peeled e` は `mixedGatePeel` で剥がした本体（インスタンス述語が最初に問われる点）。

### 33.2 証明できたもの（標準 axiom のみ。`http_gates_V`/`tlp_gates_Vi` は propext のみ）

| 名前 | 内容 |
|---|---|
| `http_gates_V`、`http_gates_Vi`、`tlp_gates_V`、`tlp_gates_Vi` | 閉じた宣言（型 `T`、値 `V` または inliner 後の `Vi`）上で `certifiedShape?` と `mixedCertifiedShape?` が `none`。**kernel 評価**（`with_unfolding_all rfl`）。インスタンス述語 `ip` は抽象のままで、`ip (peeled V) = false` の 1 点だけを使う（他の点は問われない: 証明が通ったことが根拠） |
| `entryGates_of_two` | `RootInEnv`、inliner の 2 事実、「宣言上の gate」と「inliner 後の宣言上の gate」から `EntryGates env X`。`entryConst` はどちらを返しても gate が通る（`machineShape?` の評価は不要。S1l の `entryOfDecl_inl` の `hs` を要さない） |
| `httpGate_of_facts`、`tlpGate_of_facts`、`hftKidsGates_of_facts` | `KidGateFacts` から `EntryGates`、`HftKidsGateFacts e → HftKidsGates e` |
| `HftFinalStmtOffLNKKG`、`synth_hftPcieOutByte_finalOffLNKKG`（`_Z/_Y/_X`） | S2d の最終文の `hkgates : HftKidsGates (envAt cref w)` を `hkgfacts : HftKidsGateFacts (envAt cref w)` に替えたもの |

**binder 一覧（`finalOffLNKKG_Z`、明示仮説 14）**: `hlink L lvl env₀ hstart hr hcell hchk hreadH hreadT hcd htop hkenv hkgfacts`（S2d の `hkgates` だけが `hkgfacts` に替わった。個数は同じ）。`hreadH`/`hreadT`（`RootReader`、`machineShape?`/`dataOfAt` の部分）は既存の仮説のまま。

### 33.3 残る名前付き仮説（impossible とは言わない）

`hkgfacts : HftKidsGateFacts (envAt cref w)`（FG D.T-4g）: 被呼び出し 2 つ × 5 事実 = **10 の環境の事実**（`envAt cref w` の 1 つの環境に対し、各事実は 1 つの閉じた項または 1 つの名前での問い合わせ）。all-world の law ではなく、`ReadsAt`/`Start`/`CheckedStart` は含まない。Check27 が build の環境で 10 事実すべてを観測（MetaM、供給ではない）。残りは S2d から変わらない `hkenv`（D.T-4k）、`HftRootLink`（S2c）、`hcd`（S2b）、`htop`、`hreadH`/`hreadT`、`hchk`、`CellPrem`、`Laws`/`Start`/`hr`。

### 33.4 Check27 の出力（`kjob lake build Tests.Gen5.FGCircuitPilotCheck27`、exit 0、933 jobs）

- `FGCIRCUIT27 SIGNATURES-A`: `KidGateFacts` の構成子の型と `HftKidsGateFacts` を独立に書いた `ExpKGF`/`ExpHK` と照合。**13 mutant 棄却**（点を値全体に、inliner 後の点を落とす、root を落とす、inliner の型の事実を落とす、値を宣言に結ばない、quote の入れ替え、名前の入れ替え、片方の被呼び出しを 2 回、片方のみ、値全体の点、`True`）。
- `FGCIRCUIT27 SIGNATURES-B`: `finalOffLNKKG_Z` の 14 仮説、`hkgfacts` が最後、`hkenv`/`hreadH`/`hreadT` は不変、`MachineDefines`/`HftKidsDefine`/`MachineCloses`/`Start`/`ReadsAt`/`CheckedStart` が `hkgfacts` から到達不能、S2d の文と違う。**17 構造検査**。`FGCIRCUIT27 HYPS`（14 個）。
- `FGCIRCUIT27 QUOTES`: 4 つの quote が宣言の型/値と `Expr.equal`、http ≠ tlp、10 事実が環境点 1（この build）と点 2（無関係な宣言を足した後）の両方で成立（**25 検査**、観測）。
- `FGCIRCUIT27 CONTROLS`（7 件）: 入れ替えた被呼び出しは事実を破る（root が両方向で偽）、gate が通らない宣言（`gateFail`: `certifiedShape?` が `some`）の検出、インスタンス述語が問い合わせに敏感（`kidWrap`: 本物の述語では mixed gate が `some`、常に false では `none`）、本物の entry 定数は両方 gate が通る。
- `FGCIRCUIT27 REMAINING`（1 行: `hkgfacts`）、`FGCIRCUIT27 AXIOMS`: 12 名、標準 axiom のみ。

Check の出力行は 7（SIGNATURES-A 1、SIGNATURES-B 1、HYPS 1、QUOTES 1、CONTROLS 1、REMAINING 1、AXIOMS 1）。台帳: FG 75 / T1 57（今回 FG -0 +0 / T1 -0 +0）。成果は条件付き。

### 33.5 次

`hkenv` (A)/(B)（D.T-4k）、`htop`、`hcd`（S2b）、`HftRootLink`（S2c）。`ui_val` の snapshot `Vi` を `userInliner` の kernel 評価に置き換える道は未調査（`userInliner` が `partial`/extern を含むため現時点で見つかっていない）。

### 33.6 ビルド環境の注記

`timeout 1500 kjob lake build TARGET`（`ulimit -v` なし）。`Tools.ShippingFGCircuitS2gGates` は約 1 分（S2d の build 込みで）、Check27 も約 1 分。
