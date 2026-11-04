# BINDER_EXIT_CENSUS 詳細（調査の原表。5 担当の出力をそのまま載せる）

本体は BINDER_EXIT_CENSUS.md。ここは各行の根拠の全文（読み取り専用の調査。Lean は走らせていない。「読み」と「確認」の区別は各行に従う）。台帳の数・文は変えていない。

---

## 担当 1

### out_1: A.P-* 23 行の束縛変数の出口（読み取り専用の調査）

base = par/hord-run@392dc221（以下「base」）。「読み」= ファイルを読んで判断、「確認」= base 内（または指定 branch）で定理の署名・本体を読んだ（Lean は走らせていない）。
分類: R = run 等から出せる / P = 既存の証明済み定理か既存の台帳行に置換 / D = パッケージのデータ（data-supply 系）/ U = 経路が見つからなかった / X = 現時点で一般定理から支払い不可。
「見つからなかった」は、この調査で辿った範囲（refs/heads と refs/remotes の Tools/ の grep）で供給元・経路が見つからなかったという意味。不可能の主張ではない。

前提として確認したこと（行ごとの根拠で共通に使う）:
- base には `StepStmtCases` / `stepStmtCases_of_rows` / `StepLift` が無い（Tools/ に `Gen2Step*` ファイル無し）。これらは kjob/g2st-r6@2be39bc4（`Tools/ShippingGen2StepDispatch.lean:41/48/63`）にだけある。
- T1 の組み立て `ihAt_stepPF` / `t1_of_stepPF`（base `Tools/ShippingGen2T1.lean:187,189,242,244`）は、`StepStmt` の前件 `MachineTaken` を `machineRunJQC_of_closesA … hT.closes` で、`hdec` を `hT.dec` で、`MachineDefines` を `hT.defines` で出している（確認）。StepStmt の run 系前件は T1Hyp の field に帰着する。
- FG_CONNECT（base `Tools/ShippingGen5FG.lean:54-66`）は T1 の行を束縛変数に持たない。結論 O1/O2/O3 を証明する側の型で、`EntryWitness` は保証の前件（確認）。

## 表

| ID | 束縛変数（Lean 名: 型の要点） | FG 側の定理 file:line @branch:SHA | 分類 | 根拠（読み / 確認） |
|---|---|---|---|---|
| A.P-01 | `L : Laws mref cref`（`O : RefLawsAOps`, `T : RefLawsATele`）。文脈の束縛変数 | 全定理（`FG_CONNECT` `Tools/ShippingGen5FG.lean:54` @base、`StepStmt` `Tools/ShippingGen2Defs.lean:316` @base） | X | TRUSTED 境界（T1L-01 と共有）。run の事実ではない（T1 台帳 T1L-01 の「no (a law is not a run fact)」）。新しい law を足さずに外す経路は無い。読み |
| A.P-02 | `Start L mctx cctx w`（= `AdmCtx ∧ JQC L.O 0 w`）。`EntryWitness` の 1 つ目の連言（A.P-03, C.RR-1, B.F-2, D.E-11, D.D-6 を統合） | `EntryWitness` `Tools/ShippingGen5FG.lean:32-40`、`FG_CONNECT` `:54-66` @base。読む側 `Tools/ShippingGen5DCEntryW.lean`（U-ENTRYW）@base | X | 保証の前件（スコープ）で、供給する対象ではない。FG の定理はこれを仮定して結論を出す形。T1L-02 と同じ。確認（定義） |
| A.P-04 | `RunsTo (synthesizeCombinational declName) … ∨ RunsTo (synthesizeCombinationalWithParameters declName parameters) …`。`EntryWitness` の 2 つ目の連言 | 同上。default route の分解 `synthesizeCombinational_postT1`（`Tools/ShippingGen5DCEntry.lean`）、`synthesizeCombinational_postEntry`（`Tools/ShippingGen5DCEntryD.lean:28`）@base | X | 前件そのもの。default の run から core run と `PostT1`/`PostEntry` が出る（確認、証明済み）が、前件を消す定理ではない。parametric 枝は後処理の扱いが未承認（B.P-* 側）。読み |
| A.P-05 | carrier `Post : Module → Module → Prop` | `FG_CONNECT` O1 `∃ raw, Post b raw` `Tools/ShippingGen5FG.lean:57-58`、`o1_default` `Tools/ShippingGen5DCEntry.lean:46` @base | U | default route の `Post := PostT1/PostEntry` は証明済み（確認）。parametric 枝の後処理と `Post` の採用は未承認（`Tools/ShippingGen5DCEntry.lean` の記載「not a final adoption of `Post`」）。ユーザー判断が要る部分あり。読み |
| A.P-06 | `T1Hyp.defines` の closure: `∀ c, TgtRun … c → ∀ q, GP … c = some q → ∀ mctx' cctx', AdmCtx → MachineDefines mctx' mref cctx' cref c q.d.shape`（`h_A_P06`）。C.RR-3, D.D-9 を統合 | `FGLedgerPremisesStmt` `Tools/ShippingGenFGLedgerPremises.lean`（型だけで定理ではない）@base。消費側 `closingRun0_of_runR` の `hT : T1HypND` `Tools/ShippingGen5ClosingRun3.lean:44` @base、`auditE6_of_defines'`（par/aud-ua2-impl@fc6c193b） | U | `MachineDefines` は全 world・全 env に対する文（`Tools/ShippingMachineEntry.lean:2345`）で、1 本の run からは出ない。逆向き（`MachineDefines` から run の `shapeEq`）は `runReads_of_run` で出ている（hord-run の材料）。`MachineDefines` を出す候補は `machineDefines_of_readsAll`（`Tools/ShippingGen5Env.lean:69` @base）だが、`hall : ∀ u, ReadsAt env₀ cref u`（B-ENV の C.EN 行の領域）と `hg1 hg2 hsh`（パッケージの shape 側 = G3-SHAPE, T1L-33/34）を仮説に取る。C.EN 側は調査 U-A〜U-F が 0 または見送り（比較資料 §4.3）。確認（署名）/ 読み（行の対応） |
| A.P-07 | `ran : MachineTaken L mctx cctx (dv w + 1) p.decl p.d.shape raw D`（= `MachineRunJQC`）。T1Hyp.closes: `MachineClosesAtA L.O mctx cctx c q.d.shape`（C.AC-6 を統合） | 取る側: `memParent_ships` `Tools/ShippingGen2MemShips.lean:90`、`oneOut_topShipsO` `Tools/ShippingGen2OneOutTopO.lean:336`、`group_childShips` `Tools/ShippingGen2GroupServed.lean:295` @base、`StepStmtCases` `StepDispatch.lean:48` @kjob/g2st-r6:2be39bc4（前件）。出す側 `machineRunJQC_of_closesA` `Tools/ShippingServedRealA.lean:97` @base | P | 確認: `stepStmtCases_of_rows`（`StepDispatch.lean:63`）は `ran` を束縛変数に取らず `intro` する。T1 の組み立て `Tools/ShippingGen2T1.lean:242-244` が `ran` 相当を `hT.closes` から出す。FG 側に独立した束縛変数が無い（FG 台帳 A.P-07 の記載「FG には直接の binder がない」と一致）。実体は T1L-08（親）で、T1L-21, 23, 25 が残る（20, 22, 24 は解消済み）。A.P-22（FG 台帳 §12.7）と同じ形。ただし T1L-08 の中身（`MachineClosesAtA` の供給）は FG の仕事ではない |
| A.P-08 | `T1Hyp.pkg : ∀ c, Reach c → ∃ q, P c = some q ∧ q.decl = c ∧ DataOk q`。値 `p : Pkg`（`GenFacts` 等）、`hP : P c = some q`。C.CR-2 `hGen`、D.D-3 `GP` が FG 側の支払い先 | 取る側: `callDec_of_hPointG_at` `Tools/ShippingGen2CallField.lean:131`、`callDec_of_callTie` `Tools/ShippingGen5T2Tie.lean:298` @base。FG_CONNECT の O2 `∃ p, GP … = some p` は結論側（`Tools/ShippingGen5FG.lean:62`） | D | 一般の `GP` / 生成器の健全性（G3-GEN）は定理として無い（`nv_gp` は `GP := none` が反駁されることを示すだけ、確認）。`GenFacts` は「NOT derived generically」（FG 台帳 A.P-08 の読み）。`Pkg.ok` / `Pkg.body_eq` は `Pkg` の場合分け定理（`Tools/ShippingGen2Pkg.lean:88,94`）で、パッケージが与えられた後の事実。パッケージの存在は run から出ない。読み |
| A.P-09 | `DataOkB` の行と callDec 系の `hok : p.d.ok = true`、`hco : p.d.callsOk p.kD = true`、`hslots : p.d.ss.length = slots.length`（束。DataOkB は `ok, letsAliasOk, callsOk, ss.length, outTy, outHead`） | `callDec_of_hPointG_at` `Tools/ShippingGen2CallField.lean:131-139`（`hok hco hslots hargsK hlenK`）、`callDec_of_callTie` `Tools/ShippingGen5T2Tie.lean:298`（`p.ok` を使い `hok` 無し）、`stepDec_of_ties` `:312`（`hG_DATA_CALL_co`, `_slots`）@base。`Pkg.ss_length` `Tools/ShippingGen3DataSupplyK1.lean:31` @kjob/k1-pa:861c90ab（受入済み・base に未統合） | P（部品別に P/R/D） | 部品ごと: `hok` = `Pkg.ok`（定理、確認 `Pkg.lean:88`）で束縛変数は消えている（`callDec_of_callTie` は `p.ok`）。`hslots` = `Pkg.ss_length`（K1 で T1L-40 解消、k1-pa で確認）。`hco` = T1L-39（`stepDec_of_ties` の `hG_DATA_CALL_co` と同じ文、確認）。`outTy` = R（`outTy_of_core`、A.P-10 参照）。`letsAliasOk` = T1L-32 / T1L-75（D）。`outHead`（出力名が `i` で始まらない）は対応する T1 行も run 経路も見つからなかった（U。`DataOk` は抽象 Prop のままで、`DataOkB` は SrcPkg 用の具体 DataOk）。部品ごとに既存行（T1L-39, 32, 75）か定理（`Pkg.ok`, `Pkg.ss_length`, `outTy_of_core`）に落ちる。新しい行は増えない |
| A.P-10 | `hdata : MemParentDataOk p`（5 行: `ok, callsOk, ss.length, outTy, binders.drop kD ≠ .domain`）。T1 側 `hMemRow : ∀ q, DataOk q → MemParentDataOk q ∧ ExtInS q`（T1L-12） | 取る側: `memParent_ships`、`oneOut_topShipsO` `:336`、`oneOut_childShips` `Tools/ShippingGen2OneOut.lean:288`、`group_childShips`、`oneOutSl_topShipsNC` `Tools/ShippingGen2SlotlessTop.lean:447` @base。束ねる側 `stepStmtCases_of_rows` `StepDispatch.lean:63`（`hMemRow` `hOneRow`）@kjob/g2st-r6:2be39bc4。`auditE3B3_of_t1hyp_run` `Tools/ShippingGen5AuditE3B3Run.lean:276`（`hMemRow` を仮説に取る）@base | D（部品別に R/P/D/U） | 確認: `stepStmtCases_of_rows` の `hMemRow`/`hOneRow` は T1L-12 の文そのもの（`∀ q, DataOk q → MemParentDataOk q ∧ ExtInS q`）で、FG の `hdata` は `hMemRow p hD` から出る。FG の独立した束縛変数ではなく T1 root の束縛変数。部品: `ok` は `Pkg.ok`（P）、`ss.length` は `Pkg.ss_length`（P、k1-pa）、`outTy` は **R**: `outTy_of_core`（`Tools/ShippingReaderOutsInv.lean:137` @base。署名 `hcore : RunsTo (synthesizeCombinationalCore c [] false) … → entry : MachineDefines … → ∀ o ∈ shape.layout.outs, o.ty.bitWidth = o.width`、StepStmt の `hcore` `hdef` と同じ引数）、`callsOk` は T1L-39（D）、`binders.drop kD ≠ .domain` は T1 に一般の行が無い（`scripts/gen5/AUD_UA4_STUDY3.md` §1。U）。5 行のうち run か定理で出るのは `ok, ss.length, outTy` の 3 つ、残りは `callsOk` と `.domain`。行そのものは消えない |
| A.P-11 | `hdata : LeafDataOk p`（4 行: `ok, callsOk, ss.length, outTy`）。T1 側 `hLeafRow`（T1L-11） | `leaf_ships` `Tools/ShippingGen2Leaf.lean:274`、`slotlessLeaf_ships` `Tools/ShippingGen2SlotlessLeaf.lean:440`、`slotlessLeaf_topShipsNC` `Tools/ShippingGen2TopNC.lean:239` @base。`stepStmtCases_of_rows` の `hLeafRow` @kjob/g2st-r6:2be39bc4 | D（部品別） | A.P-10 と同じ構造。4 行のうち `ok`（P）、`ss.length`（P）、`outTy`（R）は出る。残りは `callsOk`（T1L-39, D）。`hLeafRow` は T1L-11 の文そのもの（確認 `StepDispatch.lean:63-66`）。`ExtInS` の連言は A.P-12 |
| A.P-12 | `hext : ExtInS p`（`p.extBS i bools bits j = bools j`、`p.extS … j n' = bits j n'`（`j < p.kD`））。T1L-11/12 の `∧ ExtInS q` | `leaf_ships`、`memParent_ships`、`slotlessLeaf_ships`、`oneOut_childShips`、`group_childShips`、`groupSl_childShips` @base。定義 `Tools/ShippingGen2MemParent.lean:46` @base | D | `ext` / `extB` は `SrcPkg` の field（`Tools/ShippingGen2SrcPkg.lean:50-53`、生成器が与える関数）で、`GenFacts` に `ExtInS` に当たる文は無い（読み）。`CombPkg` は `extS` / `extBS` を恒等として定義している（`Tools/ShippingGen2CombPkg.lean:98-100`、読み）ので `.comb` は定義から出る見込みだが、`.gen` / `.loop` の一般供給は見つからなかった。`ExtInS` を結論にする定理は grep で見つからなかった |
| A.P-13 | `hmo : MemOrigin p`（`∀ k, ∃ cb aw dw, originAt … = some (memModule cb aw dw) ∧ bsIn … = some (.bits dw)`） | 取る側 `memParent_ships`（`MemParentStmt'`）。出す側 `memOrigin_of_memDec [Nonempty ι]` `Tools/ShippingGen2MemFacts.lean:51` @base。使う側 `stepStmtCases_of_rows` `StepDispatch.lean:63-` @kjob/g2st-r6:2be39bc4 | P | 確認: `stepStmtCases_of_rows` の本体が `have hmo : MemOrigin p := memOrigin_of_memDec p hmd` で出し、`hmo` を束縛変数に持たない。空の `ι` は `stepConclusion_of_empty`。材料は A.P-16（MemDec = T1L-26）と `Nonempty ι`（T1L-41）。循環なし。base には `stepStmtCases_of_rows` が無い（g2st-r6 のみ）。`memOrigin_of_memDec` 自体は base にある |
| A.P-14 | case 前提 `insts = []` / `instFields = []` / `layout.slots = []` / `Nonempty ι` / `StepCaseOK p`（L1/L2, M, O1 の 3 形） | `StepCaseOK` `StepDispatch.lean:41`、`StepStmtCases` `:48`、`stepStmtCases_of_rows` `:63` @kjob/g2st-r6:2be39bc4。case X の除去 `caseX_run_absurd` / `stepStmt_of_noX` `Tools/ShippingGen3T1L18Conn.lean:49,76`、`runShape_noMemRow` `:21` @par/t1l18-conn:29b9e301 | U（一部 R） | 確認（t1l18-conn のコード）: `runShape_noMemRow`（run の `shapeEq` と `machineShape?_noMemRow`（base `Tools/ShippingGen3HrowGate.lean:109`））で `noMemRowS shape` が出て、`hord_of_rowS`（base `Tools/ShippingGen2DataBridge.lean:43`）で O1 形の `hord` が run から出る。`caseX_run_absurd` で instFields=[] の memory call（case X）は矛盾（T1L-18 は除去済み）。→ O1 形の `hord` 連言と case X は R で消える。残り: 群（group）親 G0/G1 の `TopShips`（instFields ≠ [] の通常 call を含む）、case S（C5S）、one-output slotless の実 Pkg（D4）は、`TopShips` を結論にする定理が見つからなかった（`group_childShips` `groupSl_childShips` は `ChildShips` だけ。refs の grep で `group*topShips` 無し）。T1L-15/16/17 が未被覆 case の T1 行（name のみ）。A.P-14 の行は残る。`Nonempty ι` は T1L-41 |
| A.P-15 | `hrst : "rst" ∉ raw.inputs.map (·.name)`、`ptop_inst` の `hnoRst` `hnoClk`（case C の前提） | `oneOutSl_topShipsNC` `Tools/ShippingGen2SlotlessTop.lean:447-468`（`hrst` 束縛変数）@base、`ptop_inst`（kjob/g2tc-ptop19@c5c37d2b） | U | `rst` が入力かどうかは宣言の入力で、run の事実ではない（run から `rst ∉ inputs` を出す補題は見つからなかった）。`TopShipsNC → TopShips` は無条件（`topShips_of_NC` `Tools/ShippingGen2TopNC.lean:74` @base）。`rst ∈ inputs`（case S）の `oneOutSl_topShipsS` は全 ref の grep で見つからなかった（T1L-17）。A.P-15 の束縛変数は T1L-17 の補集合（case 制限）で同じ前提ではない（FG 台帳 §9.3） |
| A.P-16 | `hmd : ∀ k, MemDec p k (p.d.shape.insts[k]).1`（`MemDec`: `∀ i bools bits, MemFacts …`）、`hdec` の左 disjunct。D.T-11 `hG_MEMCALLS` を統合 | `memParent_ships` @base、`stepStmtCases_of_rows` の `hdec` 前件 @kjob/g2st-r6、`stepDec_of_ties` の `hG_MEMCALLS` `Tools/ShippingGen5T2Tie.lean:312` @base、定義 `Defs:122` | D | `MemDec` を結論にする定理は全 ref の grep で見つからなかった（`memFacts_of_memDec`, `memOrigin_of_memDec` は消費側）。履歴上の供給は宣言ごとの kernel チェック（`lm_memDec`, `q_memDec`、生成器の `memTactic`）。T1L-26 と同じ前提（T1 §8 が `hG_MEMCALLS` と同じと記す）。case X の absurd（A.P-14）は instFields=[] の MemDec を否定するだけで、MemDec を供給しない |
| A.P-17 | `hdec : ∀ k, MemDec … ∨ ∃ q, P … = some q ∧ CallDec p q k`（T1Hyp.dec = T1L-09 親）。`CallDec`（`Defs:108`） | `StepStmt` `Defs:316` @base、`stepStmtCases_of_rows`（前件）、`allCallDec_of_hord` `StepCases.lean:43` @kjob/g2st-r6。出す側（条件付き）`stepDec_of_ties` `Tools/ShippingGen5T2Tie.lean:312`、`callDec_of_callTie` `:298`、`callTie_of_served` `:276`、`hPointG_of_callTie` `:291` @base | P（PA） | 確認: `stepDec_of_ties` は `hdec` を `hDG_PKGASSIGN`（C.DG-1 / D.D-3 の領域）、`hT2_TIE`（`CallTie` ← `callTie_of_served` ← `hDG_GENP`, `hDG_CLOSINGRUN`, `GenExtAtCall`（D.T-1）, `CallOutRange`（D.T-2））、`hG_DATA_CALL_*`（A.P-19, A.P-09）、`hG_MEMCALLS`（A.P-16）から組み立てる。葉は A.P-16, A.P-18, A.P-19, D.T-1, D.T-4（台帳の記載どおり）。ただし T1Hyp.dec は FG 台帳 §12.11 の A.P-24 置換が使っている行（`ihAt_stepPF` が `hT.dec` を使う、`Tools/ShippingGen2T1.lean:189`）。ここで `dec` を `stepDec_of_ties` に置き換えると `hDG_CLOSINGRUN`（ClosingRun）→ IH → `dec` の循環の有無が未確認（IH は深さを下りる向きに見えるが確かめていない）。置換は候補止まり |
| A.P-18 | `HPointAt` / `HPointG P p q k` / `CallFactF`（呼び出しごとの生成残差 G3-GEN-CALL）。D.P2（LetTie）, D.P3（CallOut）を統合 | `callDec_of_hPointG_at` `Tools/ShippingGen2CallField.lean:131`、`hPointG_of_callTie` `Tools/ShippingGen5T2Tie.lean:291`、`callTie_of_dgen` `:259`、`letTie_dec`（`Tools/ShippingGen5T2Dec.lean`）@base。`LetTie` / `CallOut` の生成器 family 版 @par/gen5-t2:0bb53938 | D | 確認: `HPointG` の束縛変数は `CallTie`（`LetTie ∧ CallOutF`、`T2Tie.lean:231`）に置換されている。`LetTie`（t2）は `letTie_dec` で decoded family 上は証明済み。`CallOutF`（t1+t3）は `callTie_of_dgen` で `hT2_FIELD`（`callField_at` で served 結果から）、`hDG_SEM : GenExtAtCall`（D.T-1、未供給）、`hDG_SEM_range : CallOutRange`（D.T-2）に分解。残るのは D.T-1 / D.T-2（→ A.P-25 と D.T-4）で、生成器の family（`ArgFamB` / `ArgFamV`）に対する LetTie は固定されていない（UN-C）。生成器の意味（DG-SEM）側 |
| A.P-19 | 呼び出し対 data: `hargsK : callArgsOkAt p.d p.kD k q.portWidths = true`、`hlenK : (insts[k]).2.1.length = q.ports.length`。global `widths / hargs / hw / hlen`。D.T-10 `hG_DATA_CALL_*` を統合 | `callDec_of_hPointG_at` `CallField.lean:131-139`、`stepDec_of_ties` `T2Tie.lean:312`（`hG_DATA_CALL_args`）@base。出す側 `dataCallAt_of_trace_S3` / `callArity_noIota_of_trace`（`Tools/ShippingGen3DataSupply16.lean:84,63` @kjob/flowb-b:83820d32）、`dataCallAt_of_trace_K1`（`Tools/ShippingGen3DataSupplyK1.lean` @kjob/k1-pa:861c90ab）。`ArgWidthAt` `Tools/ShippingGen3ArgWidthSrc.lean:176` @base | R（arity 部分）+ U（args 部分） | 確認（k1-pa / flowb-b のコード）: `DataCallAt` の 4 行のうち、arity `length = q.ports.length` は `StepStmt` の served trace `h`（`MachineTraceLBX (ServedP (ShipsRes L P) …)`）から `callArity_noIota_of_trace` で出る（R）。`hco` は T1L-39、`hss` は `Pkg.ss_length`（P）。残る `callArgsOkAt … q.portWidths = true` は `dataCallAt_of_trace_S3` の仮説 `hARGW : ArgWidthAt P p k` そのもの（`ArgWidthAt` の定義が当該の式、base `:176-178`）で、これを出す補題はこの調査で見つからなかった（T1 台帳 T1L-27: source 側 width は unknown）。k1-pa と flowb-b は受入済みだが base に未統合。さらに trace `h` は `hT.dec` を使う `servedShips0_run` 由来なので、`dec` を組み立てる側（A.P-17 の `stepDec_of_ties`）に使うなら循環の確認が要る（未確認） |
| A.P-21 | （retired）`group_childShips` に `hseq` 束縛変数は無い | `group_childShips` `Tools/ShippingGen2GroupServed.lean:295-306` @base | P（retired） | 確認: 署名に `hseq` は無い（`hdata hext hins hfe hsl hA hpost ran hdec n h`）。台帳どおり |
| A.P-23 | `hlift : LiftShips L P`（`∀ c r m n q, m ≤ n → RealChildA L.O c r → P c = some q → q.decl = c → ChildShips q m r.1 r.2 → ChildShips q n r.1 r.2`）、および `group_childShips` の `h`（`ShipsAt L P n` 版 trace） | `servedP_lift_of_liftShips` `StepLift.lean:36`、`liftTrace_of_liftShips` `:85`、`LiftShips` `:25` @kjob/g2st-r6:2be39bc4。`group_childShips` `GroupServed.lean:295`、`groupSl_childShips` `SlotlessParentRun.lean:340` @base。base に `LiftShips` は無い（grep） | U | T1L-19 と同じ文（T1 root の束縛変数、T1 台帳 §11.3 の型案 `-- T1L-19`）。`LiftShips` を結論にする定理は見つからなかった（`LiftShipsInstFree`（g2st-r5）は別の弱い文で `liftShipsInstFree_proved`、`LiftShips` を供給しない）。`LiftShips` が必要になるのは群親 G0/G1 の枝（A.P-14 の未被覆 case）だけなので、A.P-14 の group 枝が閉じない限り消費されない（読み） |
| A.P-25 | `hW : ∀ k, OneOutWidth P p k`（callee の唯一の出力幅 = 親の call 結果 binder の幅）。D.T-3 `hOW` を統合。T1 側 `hWRow`（T1L-14） | `oneOut_topShipsO` `OneOutTopO.lean:336`（`hW`）、`oneOutSl_topShipsNC` `SlotlessTop.lean:447` @base。`stepStmtCases_of_rows` の `hWRow` @kjob/g2st-r6。`oneOutWidth_of_strict` / `oneOutWidth_of_strictP` `Tools/ShippingGen2DataBridge.lean:123,142` @base | D | 確認: `oneOutWidth_of_strictP` は `hW` を Bool 行 `callWidthsStrict p.d p.kD (kidOutsP P p) = true` と `hsimple : instFields = []` に置き換える（定理、base）。この行は package 上の decided row で、run から出る補題は見つからなかった（`ChildPortWidths` は callee の入力ポート幅で、出力幅 `OneOutWidth` は別の文、確認 `Defs:83`）。`callWidthsStrict` はコンパイラが検査する行ではない（hrow-gate のような最終ゲートは無い、読み）。ゲートを足す案は共有定義/コンパイラの変更でユーザー判断が要る（X）。`hWRow` は T1L-14 の文そのもの |
| A.P-27 | `TopShips` 結論内の実行前件 R-G（`SourceInputs`, `regs` 固定, `rst/clk` ガード付き, `st0 = f.init`, `ResetNk`, `ins` の幅, `st0` の幅）と `PTopPrem` | `TopShips` `Defs:288-312` @base。`PTopPrem` / `ptop_inst` / `ptop_prem_ofRun` / `ptop_ofSlotlessRun` @kjob/g2tc-ptop19..14（base に無し）。base に `Tools/ShippingGen2TopVacuity.lean`（`topShips_iff_inner` 等） | U | 結論側の前件で、定理の束縛変数ではない（FG 台帳 A.P-27 の記載と一致）。非空虚性の監査（`ss = []` の c2/c3, c6, c1/c5, c4 の部分補題は g2tc 系にある）。slotted（regs ≠ []）の c2/c3 は見つからなかった。一般の行は証明で消える種類ではない（X 相当の面あり）。読み |
| A.P-28 | `hex : PbhRunEx L`（具体 run の存在と共同充足性）。T1L-70 と共有 | `ptop_pbh_ofEx`（kjob/g2tc-ptop19@c5c37d2b）、`not_pbhRunEx_lawsQuietFalse`（`Tests/Gen2/TopLawsQF.lean` @kjob/g2tc-ptop21:22862066）。base に `PbhRunEx` 無し（grep） | U | 非空虚な `Laws` の値・具体 run を作る定理は見つからなかった（`lawsQuietFalse` では偽と証明済み）。監査の行で、一般定理から払う種類ではない。読み |

## 分類の件数

- 主分類: P 5（A.P-07, 09, 13, 17, 21）、R 1（A.P-19 の arity 部分。args 部分は U）、D 7（A.P-08, 10, 11, 12, 16, 18, 25）、U 7（A.P-05, 06, 14, 15, 23, 27, 28）、X 3（A.P-01, 02, 04）。合計 23。
- 束の中に R で消える部品を持つ行: A.P-09/10/11 の `outTy`（`outTy_of_core`）、A.P-14 の O1 の `hord` と case X（`runShape_noMemRow`, `caseX_run_absurd`）、A.P-19 の arity（`callArity_noIota_of_trace`）。いずれも行そのものは他の部品が残るので消えない。
- T1 区分（A.P-07..12, 14, 15, 16, 19, 23, 25）で FG 側に独立した束縛変数が無いと確認できたのは A.P-07（T1Hyp.closes）、A.P-10/11/25 の `hMemRow/hLeafRow/hOneRow/hWRow`（ただし該当定理は g2st-r6 にだけある）。A.P-14, 15, 23 は T1 の行が「補集合」または未被覆 case の行で、置換になっていない。

## R/P の有望候補

行そのものが消えるのは候補 1, 2 だけで、どちらも Lean の新規コードではなく「FG 側に独立した束縛変数が無い」ことの確認（A.P-22 の §12.7 と同じ規則）。Lean を書く候補 3, 4 は行を消すところまで届かない。

### 候補 1: A.P-07（MachineTaken / T1Hyp.closes）を「FG 側に独立した束縛変数が無い」として非リーフから除く

- 消える ID: A.P-07（C.AC-6 は統合済み）。
- 消える条件: reviewer が A.P-22 と同じ規則（FG 側に独立した束縛変数が無く、T1 側の T1L-08 で数えている）を認めること。Lean の変更は無い。
- 残る条件: T1L-08（親）。その葉 T1L-21, 23, 25（T1L-20, 22, 24 は解消済み）。`MachineClosesAtA` の供給は FG の仕事ではなく T1 側。
- root theorem の型案: 新規なし。根拠は既存の `ihAt_stepPF` / `t1_of_stepPF`（base `Tools/ShippingGen2T1.lean:187-189,242-244`）が `StepStmt` の `MachineTaken` 前件を `machineRunJQC_of_closesA L.O hA hcore hdef hcl hjqc.1 …` で `hT.closes` から出していること。
- 費用: 0 行（文書のみ）。
- 確かさ: 中。A.P-22 との違いは、A.P-07 の FG 台帳の記載が「T1L-08 の親にのみ対応・リーフ単位の一致は T1 台帳が示さない」（FG 台帳 §9.3）であること。`closingRun0_of_runR` は `hT : T1HypND`（`closes` field を含む）を仮説に取るので FG の定理側にも A.P-07 の独立した束縛変数は無い（確認、`Tools/ShippingGen5ClosingRun3.lean:44`）。
- 新しい freeze / TRUSTED: 不要（数え方の確認のみ、reviewer）。
- 新しく増える行: なし。
- 同じ規則を A.P-10/11/12/25 に当てる場合: `stepStmtCases_of_rows` の `hLeafRow/hMemRow/hOneRow/hWRow` が T1L-11/12/14 の文そのものであることは確認できたが、この定理が base に無い（g2st-r6 のみ）ので、統合後に確認する必要がある。A.P-25 は FG 台帳が D.T-3 を `callOutRange_of_widths` の材料（D.T-2/D.T-4）として別に持つので、A.P-07 より確かさは下がる。

### 候補 2: A.P-13（MemOrigin）を派生行として除く

- 消える ID: A.P-13。
- 消える条件: `stepStmtCases_of_rows` を使う組み立て（kjob/g2st-r6@2be39bc4）が FG の最終組み立てに入ること。その中の `memOrigin_of_memDec`（base `Tools/ShippingGen2MemFacts.lean:51`）が `hmo` を `hmd`（A.P-16）から出す。
- 残る条件: A.P-16（MemDec = T1L-26）、T1L-41（`Nonempty ι`）。空の `ι` は `stepConclusion_of_empty`（g2st-r6）。
- root theorem の型案: 新規なし。`stepStmtCases_of_rows`（`StepDispatch.lean:63`）が既にそれ。
- 費用: 0 行（統合は coder / ユーザーの merge）。
- 確かさ: 中〜高（`hmo` が束縛変数に無いことは本体を読んで確認、Lean は走らせていない）。
- 新しい freeze / TRUSTED: 不要。数え方は C.SM-5（R0-B）に近いが、C.SM-5 は材料の行が解消済みだったのに対し、A.P-13 の材料 A.P-16 は残る点が違う（PA 行の扱いは reviewer）。
- 新しく増える行: なし。

### 候補 3: A.P-10/11 の DataOk の行を run 局所化（outTy を run から出す）

- 消える ID: なし。行は `callsOk`, `.domain`, `ExtInS` が残るので消えない。減らせるのは束縛変数の中身（`ok`, `ss.length`, `outTy`）で、台帳の数は動かない見込み。
- 型案: `stepStmtCases_of_rows` の `hLeafRow / hMemRow / hOneRow` の連言から `outTy` を外し、`outTy_of_core hcore hdef`（base `Tools/ShippingReaderOutsInv.lean:137`）で証明の中で出す。hord-run の手本 (a) と同じ形（全 `q` 上 → この run の `p`）。意味の変更なので reviewer の freeze が要る。
- 費用: 小〜中（数十行の見込み、測っていない）。確かさ: 中。
- 効果: 台帳の数は動かない。やる理由は T1 側の `DataRows` の第 3 連言（T1L-05, 29）の整理だけ。

### 候補 4: A.P-19 の arity を trace から出す（受入済み・未統合）

- 消える ID: なし（`hARGW`（args 行）が残る。T1L-27）。
- 型案: `dataCallAt_of_trace_S3`（kjob/flowb-b@83820d32）を統合し、`stepDec_of_ties` の `hG_DATA_CALL_args` の `∧ length = ports.length` を trace から出す。
- 確かさ: 中。T1L-28 は U-B1 で解消済み（T1 台帳 §12 の履歴）。
- 注意: trace `h` が `hT.dec` を使う `servedShips0_run` 由来なので、`dec` を組み立てる側（A.P-17 の `stepDec_of_ties`）に使うと循環の確認が要る（未確認）。

### 候補なし（U / X のもの）

- A.P-06: `machineDefines_of_readsAll` は `hall`（全 world で `ReadsAt env₀`）と shape 側 3 つを仮説に取る。B-ENV の行と G3-SHAPE の行を使うだけで新しい行は増えない見込みだが、C.EN 側の調査が 0 のまま（比較資料 §4.3）なので経路としては閉じない。
- A.P-14 の group 親 G0/G1 / case S: `TopShips` の定理自体が見つからなかった（T1L-15/16/17）。
- A.P-25 のコンパイラのゲート案（`callWidthsStrict` を最終ゲートで検査）: hrow-gate（T1L-04 の除去）と同じ型の道だが、コンパイラの変更でユーザー判断が要る（X、読み。この調査では案として検証していない）。

---

## 担当 2

### out_2: 担当 N=2（B.G-1,3,4,5,6,7,9,10 / B.F-8 / B.P-1,2,3,4,5,7,8 / C.RR-2、17 行）

書き方: 「読み」= ファイルを読んで判断した。「確認」= ファイルの存在・行の本文を base (par/hord-run 392dc221) または branch で実際に開いて確かめた。**Lean は build / 実行していない**（読み取り専用の調査）。「見つからなかった」は「この調査では供給元・経路が見つからなかった」の意味。mutant は出てこない。台帳の行数・文は変えていない。

## 0. 先に分かったこと（全体）

1. **B.G-*、B.F-8、B.P-* の大半は、FG の定理（`FGLedgerPremisesStmt`、Tools/ShippingGenFGLedgerPremises.lean:30-、base）の束縛変数としては現れない。** FG 側に出るのは carrier `ReflectsAll`（D.D-1）だけで、B.G-1,3-6 はその「構成要素」の行（fg.md §8.4 の R 区分）。束縛変数が出るのは供給側の定理（gate_combChildRunN 系、FbFrag 系、Layer A 系）で、それらはまだ FG に組み立てられていない（fg-assembly に Lean 無し）。したがって「FG の定理の中で束縛変数が消える」形の除去は、この 17 行のうち **C.RR-2 だけ**が今すぐ言える。B.P-1/B.P-8 は「組み立てが書かれたときに消える」条件付き。
2. **gate route の route 証拠は run から出ない。** `synthesizeFromConst_mixed_run`（Tools/ShippingGateChild.lean:34）は `old`（certifiedShape? = none）と `shape`（mixedCertifiedShape? = some）を**仮説に取って** `simp only [old, shape]` で枝を決める。run の戻り値だけでは first gate / mixed gate / machine のどの枝かは決まらない（machine route では `MachineTaken` がその役で、FG の `EntryWitness`（ShippingGen5FG.lean:32）には gate 用の同種の証拠が無い）。確認（本文を読んだ）。
3. **gate の `old/peel/he/hb/hv` は per-declaration の生成定数に対する kernel 事実**（`#gate_child` の生成器が `gate_peel` を `rfl`、`gate_old` を `rfl`、`gate_wf` を `decide` で作る。Tools/ShippingGateChildCommand.lean:81-96、確認）。`quote`（ShippingUnifiedSource.lean:370）は Term→Expr の一方向だけで、Expr→Term の復号は見つからなかった（grep: unquote/reify/ofExpr 無し）。よって D（データ供給）側。
4. **B.P-1/B.P-8 の既存の調査（par/param-legal PARAM_LEGAL_STUDY.md）は「θ := FG の `parameters`、LegalBinding を run から出す」前提で F-θ/F-top/F-kids/F-post を要求した。** しかし既存の `ParamTopShips`（ParamIface.lean、par/param-memo 014e4dc9）は `∀ θ, LegalBinding (D.addModule b) θ → ∀ D', specializeDesign … = .ok D' → …` の形で、**LegalBinding を前件に持つ**。この形を結論にすれば LegalBinding は intro されるだけで、`legalBinding_allPos`（BridgeLegal.lean:79）で AllPos θ も出る。→ 候補 B（要 reviewer: FG の parametric 側の結論型の差し替え）。

## 1. 表

| ID | 束縛変数(名:型の要点) | FG定理 file:line @branch:SHA | 分類 | 根拠・読み/確認 |
|---|---|---|---|---|
| B.G-1 | `entry : EntryDefines mctx mref cctx cref c value`（全 world の getConstInfo/getEnv 対で `entryConst … = .defnInfo d ∧ d.value = value`。B.G-8, B.F-6, B.F-7 を併合。first-gate 版は `value := quoteDecl dn names n fe` と `hwf : fe.WF`、`hn : 0<n`） | FG の定理には束縛変数として出ない（`ReflectsAll` の構成要素。ShippingGenFGLedgerPremises.lean:30 は carrier）。供給側: `gate_combChildRunN` par/gen4-gate@b3a72c91 Tools/ShippingGen4GateLeaf.lean:221、`gateReflects_shipsResI` par/gate-p123@6057dd3f Tools/ShippingGen4GateCarrier.lean（`GateEntryRow`）、`synthesizeCombinational_fragment_dz` par/fb-resume@4519e2fb ShippingGen4FbFrag.lean、`_fragment_childRunN` ShippingGen4FbFragRun.lean | **X**（package の value と環境の定数を結ぶ反射。run から出る範囲の外） | 読み。run が与えるのは「ある d が存在して `entryConst … = .defnInfo d`」までで（`EntryDefinesRunG.at_core` ShippingEntryReadsLinked.lean:225 は run 局所の形に弱めるが、`d.value = v` の `v` は package 側のまま。確認）、`v` は表の値。機械 route の `MachineDefines`（A.P-06）が FG の内側仮説 `h_A_P06` として残っているのと同種（ShippingGenFGLedgerPremises.lean）。`GateDefines` の header 自身が「生成器が endpoint の BINDER として出す（reflection は証明しない）」と書く（par/gate-p123 Tools/ShippingGateDefines.lean header、確認）。`v := run が読んだ d.value` と置く道は、G-4..G-6 が任意 Expr についての主張になり、Expr→Term の復号が見つからなかったので閉じない。first-gate 版の `hwf`/`hn` は per-declaration の decide で D |
| B.G-3 | `old : ∀ d : DefinitionVal, d.value = value → certifiedShape? false [] (.defnInfo d) = none`（`GateLeaf.old` / `GateData.Old`） | `gate_core_facts` Tools/ShippingGateChild.lean:55（base）、`gate_full_outputs` Tools/ShippingGateKid.lean:78（base）、`GateOldRow` par/gate-p123 GateCarrier.lean | **D** | 確認: 生成器が `gate_old` を `intro d hd; simp only [certifiedShape?, hd]; rfl` で作る（ShippingGateChildCommand.lean:89-92）。per-declaration の kernel 事実。run から出す道（R）は route 証拠「mixed arm を通った」が要り（0 の 2.）、それは新しい前提（gate 版 `MachineTaken`）なので候補 D（X 扱い）。`old` は ∀ d（型違いの d も含む）で、run 局所の形より強い |
| B.G-4 | `peel : mixedGatePeel value = some (bs, quote domE (inputExpr … bpos) (inputExpr … vpos) e)`（`e : Term srt`） | 同上（`gate_core_facts` Tools/ShippingGateChild.lean:55 付近）、`GatePeelRow` | **D** | 確認: 生成器が `gate_peel` を `rfl` で作る（ShippingGateChildCommand.lean:81-88）。`e : Term srt` は生成された定数 `gateTerm`。Expr→Term の復号が見つからなかった。`mixedShape_cond`（par/gate-p123 ShippingGateDefines.lean）は受理から `mixedGatePeel d.value = some (bs, body)` と `mixedGateCond` を出すが、`body` が `quote` の像だとは言わない |
| B.G-5 | `he : e.WF kb kv vw` | 同上、`GateHeRow` | **D** | 確認: 生成器が `gate_wf` を `simp (config := {decide := true}) [Term.WF]` で作る（ShippingGateChildCommand.lean:93-96） |
| B.G-6 | `hb : ∀ j<kb, ∃ name, bs[bpos j]? = some (name,.bool)`、`hv : ∀ j<kv, ∃ name, bs[vpos j]? = some (name,.bits (vw j))` | 同上、`GateHbvRow` | **D** | 読み。`bpos/vpos/vw` と `bs` の整合は生成データの性質。生成器の note「two decide on the binder positions」（ShippingGateDesignCommand.lean:263、確認） |
| B.G-7 | `hw1 : g.srt.width ≠ 1`（`g : GateLeaf`） | `gate_full_outputs` Tools/ShippingGateKid.lean:90、`gateLeaf_outTy` par/gate-p123 ShippingGen4GateOutTyR.lean（`GateWidthRow`） | **U**（候補あり） | 読み。幅 1 の出力ポートの型は `.bit` か `.bitVector 1` のどちらもあり、`d.value` からは決まらず `d.type`（`mixedGateResultScalar d.type`）が決める（ShippingGateKid.lean:20-21, 100-106）。`EntryDefines` は value しか固定しない。`gateLeaf_childShips`（GateIfaceR）は `∃ ty` を返し `hw1` を要らないので、詰まっているのは「静的な表 `Q`/`GateRec.iface` が出力型を `bitVector width` に固定している」点。候補: `GateRec` に出力型 `ty` を持たせ、`ty` と宣言の型の関係を反射する。ただし entry の反射の拡大か新しい行になる（要ユーザー判断/reviewer） |
| B.G-9 | `Q : IfaceMap ι`、`hQ : Q g.decl = some (g.ifaceOf ty)`（`gateLeaf_shipsResI`）/ `∀ ty, … → Q …`（`_of_real`） | `gateLeaf_shipsResI(_of_real)` par/gate-p123@6057dd3f ShippingGen4GateIfaceR.lean、`gateReflects_shipsResI`（Q を表 `GT` から `gateQ` で作る）par/gate-gc1@482ae0c9 / gate-p123 ShippingGen4GateCarrier.lean | **X**（要ユーザー判断: P1/P2/P3 の束。2026-11-02 に見送り） | 確認: GateCarrier.lean で `Q := gateQ ι GT`、`hQ` は `gateReflects_shipsResI` の中で `simp [gateQ, hr, …]` で出る（B.G-9 の `hQ` はこの意味で表 `GT` に置き換わる）。しかし T1 の IH は `ShipsRes` のみなので、`ShipsResI` を入れるには共有定義 `Tools/ShippingGen2Defs.lean` の 12 定義・Tools 45 ファイルの変更（GATE_P123_DECISION.md D1 案 B、par/gate-p123-decision 5772dde8）。台帳効果は (b)案で B.G-9 −1・`GateLink` +1 の**正味 0**、(a)案は −1 だが `ReflectsAll` の中身に隠れる。表 `GT` と被覆（`GateCovers`）を作る定理は無いと同資料が書く。assembler（fg-assembly）に Lean 無し |
| B.G-10 | U-G7a: `hcore : InstCore m c bsP sel wOut`（7 field の Prop）、`hcallee : ∀ dsn, … → CombChildRunN (childMap dsn.modules) dsn k c bsC […] SC`、`hsel : ∀ vals T, …` | `instParent_combChildRunN` kjob/g4gate-g5@76a8d731 Tools/ShippingGen4InstParent.lean:~234（T2 `instParent_childShipsI` は凍結文が `Design` の 2 field で elaborate 不能、reviewer 判断待ち） | **U** | 確認: InstParent.lean 冒頭に「InstCore's fields are hypotheses; no world / post-pass / source supplier, no leaf noClk supplier, no coverage, Top, M4 or FG」。FG との対応は台帳に無い（承認前）。`hcallee` は callee の `CombChildRunN`（IH 側の `ChildShipsI`）で、gate callee なら G-1..G-6 に帰着、他 route なら各 route の供給。この調査では経路が見つからなかった |
| B.F-8 | `h : ChildRunN ch₁ dsn₁ n raw bsC outsC S`（実 run の core モジュールの ChildRunN。clean-up 輸送の入力）＋ `hpr : PostReady raw k`、`hk : 0<k` | `childRunN_dz_instFree` / `childRunN_dz_postReady` par/fb-resume@4519e2fb Tools/ShippingGen4FbDzRun.lean:17,75、`synthesizeCombinational_fragment_dz` FbFrag.lean（結論内含意の前件）、`synthesizeCombinational_fragment_childRunN` FbFragRun.lean（first-gate 限定で `ChildRunN … b` を直接作る） | **X**（非 fragment）／ first-gate fragment は **P**（既存の FB-22 に置換） | 確認: FbFragRun.lean は `ChildRunN` を `ChildFnR`（`first_child_fnR`）から作り、前提は `entry`（F-6）、`hwf`、`hn`、`hS`（package の `S` との対応）。`hS` は B.F-4 の中身。非 fragment の core モジュールの挙動（`ChildRunN`）は legacy translator の意味的正しさそのもので、GENERAL_SPEC の M4 Risk「legacy route stays CONTRACT-only (G2)」（par/gen2-spec GENERAL_SPEC.md、確認）と `legacy_translate_contract`（Tools/ShippingLegacySemContract.lean:327）が現状の到達点。run（PPRel の構造）からは出ない |
| B.P-1 | `AllPos θ := ∀ p ∈ θ, 0 < p.2` | `evalM_pos` LayerA:102、`specTypeM_ok` SpecType:44、`specExprM_ok` SpecExpr:159 ほか（par/param-memo@014e4dc9）。`legalBinding_allPos` Tools/ShippingGen4ParamBridgeLegal.lean:79（承認済み 50d22e3b） | **R**（条件付き: parametric 側の結論を `ParamTopShips` 形にする。要 reviewer） | 読み。`legalBinding_allPos : LegalBinding D θ → AllPos θ` は D に依らない（BridgeLegal.lean、確認）。`ParamTopShips b D src := ∀ θ, LegalBinding (D.addModule b) θ → …`（ParamIface.lean、確認）の前件から取れる。循環なし。詳しくは §2 候補 B |
| B.P-2 | `Bound θ d`、`PosDim d`、`NonNegDim s`、`SliceOK hi lo`（DimExpr の条件） | `makeSliceExpr_sliceOK` BridgeShape:17、`sliceOK_order` LayerA:141、`specTypeM_ok`(`hp : PosDim d` `hb : Bound θ d`) SpecType:44、`specExprM_ok_aux` SpecExpr:64（par/param-memo） | **X**（PosDim 系）／ `Bound` の coverage 分は **U**（候補あり） | 確認: Elab.lean:657-676 の `extractDimExpr` は `Nat.sub`/`Nat.div`/`Nat.mod`/`Nat.pow`/`min`/`max` を `.sub .div .mod …` として出す。一方 `PosDim` は `.sub .div .mod .clog2` を `False` にする（定義は B_M4.md P-2 に原文）ので、translator が出す DimExpr は PosDim を満たすとは限らず（`W - 1` など）、run から出ない。成功仮説で代替するには `evaluate = evalM`（B1）が要るが `evaluate` は `partial`（Sparkle/IR/Type.lean:68、確認）。`Bound` の `.parameter n` 分は `legalBinding_covers`（BridgeLegal.lean:84）に「n が設計のどこかの宣言 parameter」を足せば出る。translator は保持していない Nat binder で throw する（Elab.lean:641-646、確認）ので成り立つ見込みだが、Lean の文は無い（F-top/F-kids 系の新規） |
| B.P-3 | `ExprOK θ e`、`TyPos t`、`TyBound θ t` | `specExprM_ok` SpecExpr:159、`specTypeM_ok` SpecType:44 | **X**（B.P-2 と同じ理由） | `ExprOK` の `.sliceDim` 腕は `SliceOK hi lo ∧ Bound ∧ Bound ∧ ExprOK`。`TyPos`/`TyBound` は `PosDim`/`Bound` に帰着。分類は B.P-2 に同じ |
| B.P-4 | B1-B4: `evaluate = evalM`（B1）、`specializeType`/`specializeExpr` の腕（B2, B3）、private `requirePositive`/`validateBindings`（B4） | PARAMETRIC_BRIDGE_FREEZE.md §2-3（par/param-memo）、`requirePositive_eq` BridgeLegal:44 | **X**（B1-B3: 現状の production では証明から展開できない。production の total 化 = D1 案 2、または新 TRUSTED 等式 law = 案 3 のいずれかが要り、どちらもユーザー判断） | 読み＋過去観察の記録: BRIDGE_FREEZE.md §1 に `#print DimExpr.evaluate` = `opaque …`、`rfl`/`decide`/`simp`/`unfold` が全て失敗、との観察が記録されている（私は再実行していない）。ソースでは `partial def evaluate`（Type.lean:68）、`partial def specializeType`（Specialize.lean:56）、`partial def specializeExpr`（:75）（確認）。B4 は F3 で閉じた（`requirePositive_eq`、`specValidateBindings` の mangled 名）と台帳に書かれており、残りは B1-B3 |
| B.P-5 | `T = SpecSuccessAllPositive b D := (… isSome) → ∀ θ, LegalBinding (D.addModule b) θ → SpecOk (D.addModule b) θ` | 定義のみ ParamIface.lean（par/param-memo）。FG の定理には出ない | **X**（要ユーザー判断: D3） | 読み。T を FG の一部にするかは PARAMETRIC_SPECSUCCESS_DECISION.md の D3（ユーザー判断）。`pDivOut`（`W/2`、W=1）の観察で `specializeDesign` は `.error` を返す（`#eval`、定理ではない）ので、LegalBinding から成功は出ない。範囲の縮小になる扱い（禁止）。証明では消えない行 |
| B.P-7 | I3c: `L : RefLaws mref cref`、`hC : ChildKeeps L D`、`hs : StartV L w`、`hq : L.quiet w`、`hd : L.dval w = 0`、`hA : L.aux {}`、`hw : Out0 L w` | `body_symbolic_keeps` / `core_symbolic_keeps` / `core_symbolic_triple0` / `core_symbolic_balance` / `core_symbolic_worlds` par/param-memo Tools/ShippingGen4ParamKeeps.lean:39,103,181,249,325 | **U**（候補あり） | 確認: FG の `Laws`（Defs:46）は `O : RefLawsAOps` と `T : RefLawsATele`。ParamKeeps は旧 `RefLaws`（ShippingChildInv.lean:333）上。両者のフィールドは違う（`RefLawsATele` の注記「NOT derived from the old RefLawsCore fields (a different assumption)」ShippingChildInvA.lean:296-300）。`Laws → RefLaws` の変換も `Start → Out0` の補題も base に無い（grep: toRefLaws 等 0 件、`Out0` は ShippingChildBalance.lean:103 の旧版のみ）。候補: ParamKeeps の A-family への移植（A 版の `Keeps`/`coreHead_jqcA` は machine route に既にある。ShippingGen5RunReads.lean:69）。symbolic top が子を持たない（finishSynth が `.inst` を拒否、PARAM_LEGAL_STUDY §3）なら I3c が root の結論に要るかは、この調査では確かめていない |
| B.P-8 | `LegalBinding D θ := specValidateBindings D.modules θ = .ok ()` | `legal_facts`/`legalBinding_allPos`/`legalBinding_covers` BridgeLegal:52,79,84、`specializeDesign_ok_legal` ParamIface.lean（承認済み） | **R**（条件付き: B.P-1 と同じ、`ParamTopShips` 形の結論にする。要 reviewer） | 読み。`ParamTopShips` の前件が `LegalBinding (D.addModule b) θ` そのもの（`D` は `D.addModule b` に固定される）。run→LegalBinding の経路が必要になるのは θ := FG の `parameters` と読む場合で、その場合の欠け（F-θ/F-top/F-kids/F-post）は PARAM_LEGAL_STUDY §4 に型つきで列挙されている。ただし PostTransfer（B.P-6、担当外）は Dr.addModule raw 側の成功も要るので、F-post（`dropZeroWidthModule`/`mergeChecked` が name/parameters を保つ）はそちらで必要 |
| C.RR-2 | `hr : RunsTo (synthesizeCombinationalCore X [] false) mctx mref cctx cref w (raw, D) w'`（`runReads_of_run` / `closingRun*_of_runT1` の run 仮説） | `entryWitness_left_postEntry` Tools/ShippingGen5DCEntryW.lean:34（base、header: dc15v-135aa0ac exit 0 承認）、`synthesizeCombinational_postEntry` ShippingGen5DCEntryD.lean:28（dc11v-4523f2e9 承認）、`synthesizeCombinational_parts` ShippingGateChildComb.lean:139（base） | **P** | 確認: `entryWitness_left_postEntry (h : EntryWitness …) (hl : RunsTo (synthesizeCombinational declName) … (b, D') w') : Start ∧ ∃ raw D w1, RunsTo (synthesizeCombinationalCore declName [] false) … (raw, D) w1 ∧ PostEntry b raw D D'` が base にあり、本体は `synthesizeCombinational_postEntry`（`RunsTo.bind/ite/pure` の展開、:36-47）。台帳が「橋の命題は見つからなかった」とした橋はこれ。`closingRun0_of_runT1`（ShippingGen5ClosingRun4.lean:39）の `hrun` は同じ型の core run。parametric 側は `runReads_of_run`（machine route は `!symbolicMode && parameters.isEmpty` のみ）の対象外 |

## 2. R/P の有望候補

### 候補 A: C.RR-2（P）

**修正（reviewer 2026-11-05）**: `entryWitness_left_postEntry` / `synthesizeCombinational_postEntry` は既定の `synthesizeCombinational` route だけを扱い、`EntryWitness` は parameterized route も含む。よって一般 FG の減算は parametric の橋が揃うまで 0。下の表の効果は default route 限定の見込みとして読む（本文 §2.2）。

| 項目 | 内容 |
|---|---|
| 消える ID | C.RR-2 |
| 消える条件 | root theorem が FG と同じ `EntryWitness`（default route）を取り、`hr` を `entryWitness_left_postEntry`（ShippingGen5DCEntryW.lean:34）で作る。`hr` は FG の run 仮説の言い換えで、追加の前提ではない |
| 残る条件 | parametric disjunct では使えない（symbolic の core run は `synthesizeCombinationalCoreWith Tsyn …`、ParamIface の `synthesizeCombinationalWithParameters_designTop`）。`hd0 : dv w = 0` や `hGen` は別の行 |
| root theorem の型案 | `theorem closingRun0_of_entryWitness (… closingRun0_of_runT1 と同じ …) (hEW : EntryWitness ReflectsAll L X parameters mctx cctx w w' b D') (hl : RunsTo (synthesizeCombinational X) mctx mref cctx cref w (b, D') w') : ∃ raw D w1, … ∧ ClosingRun0 …`（`entryWitness_left_postEntry hEW hl` から core run を取り `closingRun0_of_runT1` に渡す。`Start` も同じ補題が出す） |
| 費用（推定） | 小（20〜40 行の配線。補題は built 済み） |
| 確かさ | 高（補題は base にあり、header が clean build を記録。私は build していない。読みとファイルの存在の確認） |
| 新しい freeze / TRUSTED | TRUSTED 不要。freeze は配線の定理 1 本分（HORD_RUN の rev に含められる）。reviewer: 「橋の文が見つからなかった」と書いた C.RR-2 の説明の更新（行の除去として数えるか） |
| 新しく増える行 | なし |
| 注意 | C.RR-2 は「FG の仮説そのもの」の行なので、台帳が除くのは表示上の整理（リーフは動かない）。cmp.md §3 の 2 候補（A.P-26+C.CR-1、A.P-24）と同じ種類 |

### 候補 B: B.P-1 + B.P-8（R、条件付き）

| 項目 | 内容 |
|---|---|
| 消える ID | B.P-1, B.P-8（2 行） |
| 消える条件 | FG の parametric disjunct の結論を `ParamTopShips b D src`（ParamIface.lean、既存の def）にする。proof の中で `intro θ hleg D' hspec` から `hleg : LegalBinding (D.addModule b) θ` を得、`legalBinding_allPos hleg : AllPos θ`（承認済み）を Layer A の定理に渡す。run から LegalBinding を出す必要が無くなる（PARAM_LEGAL_STUDY の F-θ/F-top/F-kids/F-post は LegalBinding のためには要らない） |
| 残る条件 | (1) assembly 定理そのもの（Layer B の F1-F6）が書かれること。**今は FG の定理に AllPos/LegalBinding の束縛変数が無い**ので、行の除去は assembly が書かれて初めて言える。(2) `Bound θ d` の coverage（`legalBinding_covers`＋ translator が宣言 parameter だけを `.parameter n` にする事実、B.P-2 側）、(3) B.P-2/3 の `PosDim` 系、B.P-4（B1-B3）、B.P-5、B.P-6（`PostTransfer`、Dr.addModule raw と D.addModule b の成功の橋 = F-post）が別途必要 |
| root theorem の型案 | `theorem fg_param (… EntryWitness …) (hp : RunsTo (synthesizeCombinationalWithParameters declName parameters) … (b, D') w') (src : SrcAt) (… B.P-2/3,4,6 の残り …) : ParamTopShips b D' src`。本体は `intro θ hleg D' hspec; have hpos : AllPos θ := legalBinding_allPos hleg; …` |
| 費用（推定） | AllPos/LegalBinding 分は 1〜3 行。assembly 全体は PARAM_INV_ESTIMATE の規模（数千行の推定）で、この候補の費用ではない |
| 確かさ | 中（`ParamTopShips` の形と `legalBinding_allPos` の型は読みで合う。FG の `FG_CONNECT` 結論 `TopShips p n declName b raw D`（machine 形）を parametric 側で `ParamTopShips` に差し替えてよいかは、台帳 Q-F3 と B.P-5/6 の整理に依り、私は決められない） |
| 新しい freeze / TRUSTED | TRUSTED 不要。FG の結論型（parametric 側）の差し替えは freeze と reviewer の承認が要る。成功した特殊化は legal なので範囲は狭まらないと読むが、台帳 Q-F3 (2) は「前件にすると範囲の縮小（禁止）にあたり得る」と書いているので**要 reviewer / ユーザー判断** |
| 新しく増える行 | なし（`SrcAt`＝B.P-6 は既存の行） |

### 候補 C: B.G-9（P だが共有定義の変更。X 扱い）

`gateReflects_shipsResI`（GateCarrier.lean）が `Q`/`hQ` を表 `GT` と `GateReflects`（G-1,3,4,5,6,7 の行を表で包んだもの）に置き換える。T1 の IH を `ShipsRes ∨ ShipsResI` にする共有定義の変更（P1）が要り、ユーザーが 2026-11-02 に見送った。(b)案で正味 0（B.G-9 −1、`GateLink` +1）、(a)案は −1 だが前提が `ReflectsAll` の中に隠れる。要ユーザー判断。この調査で新しい経路は見つからなかった。

### 候補 D（候補止まり）: gate route の run 局所化

gate 版の route 証拠（`MachineTaken` の gate 版）を導入し、`RunReadsAt` 相当の読みを書けば、B.G-1 の `entry`（値の一致を除く）と B.G-3 `old` の run 局所版（`GateDefines` の `∃ dv, entryConst = .defnInfo dv ∧ certifiedShape? = none ∧ mixedCertifiedShape? = some (bs, body)`）が run から出る。ただし (i) gate 版の route 証拠は新しい前提（行が 1 つ増える）で正味 0、(ii) `peel`/`he`/`hb`/`hv` は `body` から Term への復号が見つからなかったので残る、(iii) `d.value = package の value` の反射は残る。X（新しい前提を前提にした提案）。要ユーザー判断。減算の見込みは立てない。

## 3. 件数

17 行: **R 2**（B.P-1, B.P-8。条件付き・要 reviewer）、**P 1**（C.RR-2）、**D 4**（B.G-3, G-4, G-5, G-6）、**X 7**（B.G-1, B.G-9, B.F-8, B.P-2, B.P-3, B.P-4, B.P-5）、**U 3**（B.G-7, B.G-10, B.P-7）。B.F-8 は first-gate fragment 分のみ P（FB-22）、B.P-2 の `Bound` coverage 分は U（候補あり）。

## 4. 読んだもの

- 台帳: scratchpad/B_M4.md（par/fg-ledger-sync の B_M4.md）、C_M5dg.md（RR-1..3）、fg.md §8.3-8.4 / Q-F3、cmp.md §1-§4.3。
- base (392dc221): Tools/ShippingGen5RunReads.lean（`RunReadsAt`）、ShippingEntryDefinesRun.lean、ShippingEntryReadsLinked.lean（`EntryDefinesRunG`）、ShippingGateChild.lean:34-70、ShippingGateKid.lean:76-110、ShippingGateChildCommand.lean:60-112、ShippingGateChildComb.lean:139、ShippingGen5DCEntryD.lean / DCEntryW.lean、ShippingGen5FG.lean:32、ShippingGen5ClosingRun4.lean、ShippingGenFGLedgerPremises.lean、Sparkle/Compiler/Elab.lean:636-700, 5280-5350、Sparkle/IR/Type.lean:40-100、Sparkle/IR/Specialize.lean:25-130。
- 他 branch（`git show` のみ）: par/gate-p123@6057dd3f（GateDefines, GateIfaceR, GateLeafR, GateOutTyR, GateCarrier, FirstLeafR, IfaceR）、par/gate-p123-decision@5772dde8（GATE_P123_DECISION.md）、par/gen4-gate@b3a72c91（GateLeaf）、kjob/g4gate-g5@76a8d731（InstParent）、par/fb-resume@4519e2fb（FbDzRun, FbFrag, FbFragRun）、par/param-memo@014e4dc9（ParamIface, ParamBridgeLegal, ParamKeeps, ParamLayerA, PARAM_LEGAL_STUDY, PARAMETRIC_BRIDGE_FREEZE, SPECSUCCESS）。作業コピーは scratchpad/src/ 配下（リポジトリには作っていない）。
- 読んでいない / 浅い: PARAM_FKIDS_STUDY.md と PARAM_INV_ESTIMATE.md は取得のみで本文は通読していない。GATE_SUPPLY_FREEZE.md、GATE_CARRIER_FREEZE.md、FALLBACK_SUPPLY_FREEZE.md は読んでいない。ParamLayerA/SpecType/SpecExpr の証明本体は読んでいない（署名は B_M4.md の引用に依る）。`PosDim` の原文は B_M4.md P-2 の引用。
- Lean の build / `#print axioms` は実行していない。

---

## 担当 3

### out_3: 束縛変数の出口の調査（担当 N=3、18 行）

読み取り専用。Lean は build していない（この worktree に .lake の build 成果物が無い）。したがって下の根拠はすべて「読み」で、「確認」と書いたものは無い。
「見つからなかった」は「この調査では供給元・経路が見つからなかった」の意味で、不可能・導出不能とは言っていない。mutant は出てこない。
略記: g5env-r22 = kjob/g5env-r22 b6b3206b、g5rk-r23 = kjob/g5rk-r23 221d590a、g5ac-r27 = kjob/g5ac-r27、g5do-r6 = kjob/g5do-r6 063056d6、BASE = 392dc221（par/hord-run、kjob/rt182）。

## 0. 先に結論

1. **EN 系の「第 2 の Laws L′ / env₀ / run ごとの変数」について（要求された具体的確認）**
   * `env₀` は固定できる。EntryWitness の開始 world `w` から `env₀ := envAt cref w`（`readsAt_self`、BASE `Tools/ShippingGen5Env.lean:36`）。`jq_start` / `head_jqc_start` / `start_up_of_N` は既にこの形で書かれている（`Tools/ShippingGen5EnvQ.lean` Q9, Q10、`EnvCache.lean` N4）。FG の `GP (envAt cref w)` も同じ env を使う。よって「env₀ が固定されていない」は障害ではない（読み）。
   * `L′` を run（`RunReadsAt` / `runReads_of_run`）から構成する道は、この調査では見つからなかった。理由（読み）: `QuietStrength L L′ env₀`（`EnvQ.lean:38`）は `L′.O.quiet w ↔ L.O.quiet w ∧ ReadsAt env₀ cref w` で、`L′ : Laws` を作るには `RefLawsAOps` の 9 field と `RefLawsATele` の 4 field（`Tools/ShippingChildInvA.lean:263-334`）を `quiet′` で示す必要がある。これらは全 world・全操作 `p`・全 context についての法則だが、run は特定の world 列の `RunsTo` しか与えない。`RunReadsAt`（`Tools/ShippingGen5RunReads.lean:42`）の `chain` / `shapeEq` / `gates` は、その run の w..w6 の等式しか言わない。
   * 既存の部分的な前進（BASE `EnvFrame3.lean`）: `frameT_plus`, `frameQ_plus`, `cacheSetQ_plus`, `depthSetQ_plus`, `frame_plus`, `cacheSet_plus`, `depthSet_plus`, `excOk_plus` は、`CellPrem`（C.EN-4）・`QuietStrength`・`AdmDown`・`¬ DRow` を仮説に取る条件付き。`DRow` の 13 constructor（`whnf`, `inferType`, `isClass?`, `whnfUntil`, `instantiateForall`, `mkLambdaFVars`, `mkAppM`, `unfoldDefinition?`, `reduce`, `ioEnv`, `monoMs`, `mkExprCache`, `localMk`）と `Diag`・telescope 4 field・`AdmCtx` の任意 `canUnfold?` callback は「経路未発見」（`scripts/gen5/DG_ENV_T2_FREEZE_R3.md` §1, §1.1）。`L′` を構成した Lean 項は、見た branch（par/rt-final, par/gd-int2, kjob/g5env-r22, kjob/g5ac-r27, par/gen5-t2）に無かった（`git grep` で `: Laws mref cref :=` の構成が 0 件。`QuietStrength` / `QuietStrengthA` は常に仮説）。
   * EN 系の補助 lemma が入っている Env*.lean は、BASE の closingRun / FG root の import 閉包に入っていない（BASE で `Tools.ShippingGen5Env*` を import するのは Tests/Gen5/Env*Check.lean と lakefile のみ。`Tools/ShippingGenFGLedgerPremises.lean` は `EnvFrame3` から `CellPrem` を型として使うだけ）。つまり EN-1,2,3,5,6,7,8 は「現在の FG 定理の束縛変数」ではなく、`T1Hyp.defines`（A.P-06 / T1L-07、全 world の `MachineDefines`）を ReadsAt 経由で払う計画上の補助 lemma の前提。EN-4 だけは `FGLedgerPremisesStmt` の外側 binder `h_C_EN4` として BASE に型がある。
   * 台帳が減る形で効く EN 系の出口は、候補 B（EN-3、条件付き）を除いて見つからなかった。
2. **分類の件数（18 行）**: R 1（EN-3、条件付き）、P 1（RK-1）、D 1（RK-8）、U 6（CR-2, EN-7, RK-2, RK-4, RK-7, DO-3）、X 9（CR-4, EN-1, EN-2, EN-4, EN-5, EN-6, EN-8, RK-6, DO-2）。
3. **有望候補**は 2 つ: 候補 A = C.RK-1 を C.EN-4 の `ReadWorld cref` conjunct から消す（P、新しい行は増えない）。候補 B = C.EN-3 の `hC/hE/hN` を depth 0 の根で不要にする（R、条件付き、L′ が与えられる限り）。どちらも FG 台帳の非リーフを減らすだけで、リーフ 62 は動かない。

## 1. 表

| ID | 束縛変数(名:型の要点) | FG定理 file:line @branch:SHA | 分類 | 根拠・読み/確認 |
|---|---|---|---|---|
| C.CR-2 | `Gen : ConstantInfo → Environment → Environment → Prop`（パラメータ）、`hGen : ∀ b ci envR envR' w5 w6, RunReadsAt … p.d.shape w5 w6 → Gen ci envR envR'` | `closingShared_of_runR` / `closingRun0_of_runR` / `closingRun_of_runR`（HORD_RUN_FREEZE.md §2、`Tools/ShippingGen5ClosingRun3.lean`）、旧 `closingShared_of_run` `Tools/ShippingGen5ClosingRun2.lean:70` ほか @BASE | U（候補あり、X 寄り） | 読み: `Gen` は結論 `ClosingShared` の 1 conjunct（ClosingRun2.lean:22-37 付近）と `hGen` にだけ現れ、定理の中身は使わない。`Gen := fun _ _ _ => True` と置けば `hGen` は自明になるが、「GeneratedAt を主張しない」への移動で、`GeneratedAt`（DGEN）を消費する側の前提は消えない（束縛変数の消去とは数えない）。候補経路（実在の定理名）: `genP_generated`（g5ac-r27 `Tools/ShippingGen5AccGenP.lean:96`、`GeneratedAtK K P X E p` を `entry₀ env₀ X = some E` 付きで返す。証明済みだが `GenSFacts K`・`AssignKit K` が前提）＋ `ci_of_readsAt`（BASE `Env.lean:44`）＋ `envR_of_readsAt`（`Env.lean:50`）。`entry₀` は `entryConst true false [] ci (instancePredicate env₀) …`（g5ac-r27 `Tools/ShippingGen5Acc.lean:27`）なので w1, w2 で `ReadsAt env₀ cref` が要り、その供給は EN 系（`ReadsSupplyAt`、g5ac-r27 `AccReads.lean`、AC-7）に帰着する。`GenSFacts` / `K` は新しい束縛変数（DG-FACTS）。root の `P` が `genP K hF` であることも要る。run だけからは出ない。 |
| C.CR-4 | `hT : T1HypND L P Reach DataOk`（pkg / defines / closes / closed の 4 field） | 同上 4 定理の `hT`。定義 `Tools/ShippingGen5T1ND.lean:35-50`、`T1Hyp.toND` `:53` @BASE | X | 読み: 束縛変数 `hT` は HORD_RUN の新定理にも残る（HORD_RUN_FREEZE.md §3「`hT` はそのまま」）。fields は FG 台帳では A.P-06（defines, TY-I）・A.P-08（pkg, T1L-06）・A.P-07（closes）ほかの行が payer で、C.CR-4 は親（PA）。消えるのは数え方だけで Lean の変化が無く、LEDGER_CROSSCOUNT_DECISION.md §2 の 9 行と同じ性質（案 A 推奨）。C.CR-4 / D.T-6 はその 9 行の表に入っていない（照合が足りない）ので、外すなら別のユーザー判断で、Lean 経路ではない。 |
| C.EN-1 | `hq : QuietStrength L L' env₀`（`∀ w, L'.O.quiet w ↔ L.O.quiet w ∧ ReadsAt env₀ cref w`） | `quiet_down`, `jq_down`, `realChildA_down`, `closesA_up`, `t1HypND_up`, `jq_start`, `head_jqc_start` `Tools/ShippingGen5EnvQ.lean:46-104`、`start_up_of_parts` `EnvStart.lean:22`、`frameQ_plus` 他 `EnvFrame3.lean` @BASE | X | 読み: §0-1。`L′` の構成に `RefLawsAOps` 9 field + `RefLawsATele` 4 field が要り、その環境保存部分に `DRow` 13 constructor・`Diag`・telescope 4 field の経路が見つからなかった（R3 freeze §1 表 5〜13 行）。`AdmCtx` の `canUnfold?` は任意関数（R3 freeze §1 末尾）。run からは出ない。埋めるなら新 law / TRUSTED / `Laws` の field 追加が要るので X（要ユーザー判断）。 |
| C.EN-2 | `hd : AdmDown L L'`、`hA' : AdmCtx L'.O.quiet mctx cctx` | `realChildA_down`, `cacheInvA_down`, `jqc_down`, `closesA_up`, `t1HypND_up`（`EnvQ.lean:42-104`）、`head_jqc_start`, `start_up_of_parts`, `start_up_empty` @BASE | X | 読み: `AdmCtx quiet mctx cctx` は `canUnfold? = some f` のとき `InertUnfold quiet f`（任意の f）を要求する。`InertUnfold quiet′ f` は `quiet` だが `ReadsAt` が崩れた world での f の挙動を言わない（R3 freeze §1）。`hA'` は `canUnfold? = none` の場合だけ `admCtx_none`（`EnvStart.lean` `start_up_empty`）で出るが、これは FG の `Start` の `AdmCtx` より狭い（C.EN-8）。 |
| C.EN-3 | `hC : CacheInvA L'.O (cv w₀)` / `hE : cv w₀ = {}` / `hN : CacheInvN L env₀ (cv w₀)` | `start_up_of_parts` `EnvStart.lean:22`、`start_up_empty` `:33`、`start_up_of_N` `EnvCache.lean`（N4）、`cacheInvA_of_empty` `EnvStart.lean:28` @BASE | R（条件付き。EN-1/EN-2 が与えられた上での話） | 読み: `Start L'` の cache 半分にだけ使う。depth 0 の根ではこれが要らない。根拠: `head_jqc_start`（`EnvQ.lean` Q10）の型は `(hq) (hA') (hS : Start L mctx cctx w₀) (hh : RunsTo (coreHead X) …) : JQC L'.O 1 w1 ∧ ReadsAt (envAt cref w₀) cref w1` で `hC/hE/hN` を取らない。`coreHead` は depth 0 で `sparkleChildCache.set {}` を実行して cache を空にする（`Tools/ShippingEntryReadsLinked.lean` coreHead 本体）。`coreHead_invAt0`（BASE `ClosingRun.lean:87-126`）の D = 0 分岐は `replace hw := hw.1`（`JQ` のみ使用、cache 半分は使わない）。`closingShared_of_run` も `runReads_of_run L.O hA hw.1 hc' …` で `hw.1` のみ。→ 候補 B。ただし `closingRun0_of_run(R)` の仮説は `hs : Start L …`（cache 半分込み）で、結論の `ClosingRun0.start0 : Start L …` も同じなので、L′ で使うには depth 0 用の「JQ だけの start」版の定理（新しい statement、`ClosingRun0` とは別の structure）が要る。 |
| C.EN-4 | `CellPrem MkRefd mref cref`（`CellOK` 3 つ ∧ SideRef ∧ Fresh ∧ `ReadWorld mref` ∧ `SetFrame mref cref` ∧ `mref.ref ≠ cref.ref` ∧ `ReadWorld cref` ∧ `SetGet cref`） | `FGLedgerPremisesStmt` の `h_C_EN4`（BASE `Tools/ShippingGenFGLedgerPremises.lean:41`、型だけ）、定義 `EnvFrame3.lean:58-63`、使用 `envFrameEnd_framedA` ほか @BASE | X | 読み: 全 conjunct が不透明な `ST.Ref.get/set` についての命題（`ReadWorld r := ∀ w, getW r w = w` 等、`Tools/ShippingStRefCorrespondence.lean:38-47`、コメントが "PREMISE for the real runtime"）。run は「その操作が return した」しか言わず、`runsTo_det`（同ファイル）も決定性だけ。TRUSTED にするか否かは DG_ENV_FREEZE §4 の A/B/C の判断で、決定の記録はこの調査では見つからなかった。型を付けても何も決まらない（台帳の記述どおり）。 |
| C.EN-5 | `¬ DRow p`（`FramedA MkRefd p` の 13 constructor の除外） | `frameQ_plus`, `envFrameEnd_framedA` `EnvFrame3.lean` @BASE | X | 読み: `DRow`（`EnvFrame3.lean:35`）は Meta ライブラリ 9 個（`whnf`, `inferType`, `isClass?`, `whnfUntil`, `instantiateForall`, `mkLambdaFVars`, `mkAppM`, `unfoldDefinition?`, `reduce`）と `IO.getEnv`, `IO.monoMsNow`, `IO.mkRef` 系 3〜4 個。R3 freeze §0-4 の `#print` で `whnf` / `inferType` は `opaque`、IO 系も `opaque`。translator の body は実際に `whnf` 等を呼ぶ（`FramedA` はそれらを含む）ので、「実行された操作には現れない」で払う道も見つからなかった（`frameQ` は全 p についての field）。環境を変えない、という Meta ライブラリの性質は新 law / TRUSTED になる。X。 |
| C.EN-6 | `hall : ∀ u, ReadsAt env₀ cref u`、`hc hg1 hg2 hsh`（env₀ 側のゲート・shape の事実） | `machineDefines_of_readsAll` BASE `Env.lean:69`（sufficient only）、`machineDefinesR_of_env` `EnvR.lean:46`、`machineDefinesR_of_defines` `:40` @BASE | X（部分的に R、下記） | 読み: `hall` は全 world の命題で、run からは出ない（EN-1 と同じ理由。全 world で保存するのは L′ の quiet の仕事）。run に局所な代替は既存: `ReadsAt.of_frame`（`Env.lean` E3）、`envFrame_getConstInfo`（`Tools/ShippingEnvSnapshot.lean:68`、`GetEnvFrame` から）、`getEnvFrame_of_readKeeps`（`Tools/ShippingStRefCorrespondence.lean`）、g5rk-r23 の `readsAt_chain_of_head`（`Tools/ShippingGen5ReadKindsU12.lean`、`hk` `hHead` `h0s` から chain の w1,w2,w3 の `ReadsAt`）。depth 0 の根では `h0s := readsAt_self`（BASE `Env.lean:36`）が使えるので `ChainReadsAt (envAt cref w) … X w`（par/rt-final `AccReads.lean`）が `hk`（RK-1）と `hHead`（RK-2）から出る。ただしそれを `MachineDefinesR` として使うには `T1HypND.defines`（T1L-07、全 world）の statement を変える必要がある（`EnvR.lean` 冒頭自身が「共有定義の変更、未承認」と書く）。さらに depth ≥ 1 の子の run の開始 world では `ReadsAt` を不変量として運ぶ必要があり（`IHAt` は任意の `InvAt` world を量化、`Gen2Defs.lean:165`）、それが L′ の仕事。→ 共有定義の変更を含むので X（要ユーザー判断）。 |
| C.EN-7 | `hentry : ∀ w1 w2 r1, L.O.quiet w1 → sv w1 = some synthesizeChild → ReadsAt env₀ cref w1 → CacheInvN L env₀ (cv w1) → RunsTo (synthesizeCombinational n) … w1 r1 w2 → L.O.quiet w2 ∧ sv w2 = some synthesizeChild ∧ CacheInvN L env₀ (cv w2)` | `synthesizeChild_realN` `Tools/ShippingGen5EnvCacheE.lean:30`（g5env-r22、BASE にも同ファイル） | U | 読み: 旧 `synthesizeChild_realA` の `hentry`（`Tools/ShippingChildCacheA.lean:300`）は T1 側で `hentryT_of_bodyP`（`Tools/ShippingChildPinC.lean:292`）、`KeepChildStmt`（`Gen2Defs.lean`）の枠で払う設計。`CacheInvN`（`EnvCacheC.lean:25`）は `RealChildN`（各 entry の保存 world で `ReadsAt env₀` と `canUnfold? = none`）を要求するので、`IHAt` / `ChildKeepsInv`（`InvAt` = `JQC ∧ CacheShips`、`Gen2Defs.lean:165-190`）からは直接出ない（`ReadsAt` が `InvAt` に入っていない）。同じ帰納法を `RealChildN` で回す姉妹版が要りそうだが、その形の定理は見つからなかった（U9 freeze 自身が「rows owned by G-REACH / DG-READKINDS は名前のみ」）。候補: 姉妹版の ChildKeeps を `RealChildN` 不変量で書く（費用は大、L′ が前提）。 |
| C.EN-8 | `hn : mctx.canUnfold? = none` | `start_up_empty` `EnvStart.lean:33`、`synthesizeChild_realN`、`cacheInvN_insert_runs` `EnvCacheD.lean:24`、`realChildN_of_run` @BASE | X | 読み: FG の `Start L mctx cctx w`（`Gen2Defs.lean:52`）は `AdmCtx L.O.quiet mctx cctx`、すなわち `canUnfold? = some f` で `InertUnfold` のものも許す。`hn` を FG に採用するのは scope の縮小（禁止、ユーザー判断）。run は context についての情報を持たない。 |
| C.RK-1 | `hk : ReadKeeps cref`（`∀ w, readOf cref (getW cref w) = readOf cref w`） | `readMachine_agrees_runReads_of_head_self` `Tools/ShippingGen5ReadKindsU13.lean:22`（g5rk-r23、BASE に無い）、FG 側の外側 binder `h_C_RK1`（BASE `Tools/ShippingGenFGLedgerPremises.lean:42`） | P（C.EN-4 の conjunct から） | 読み: `CellPrem`（BASE `EnvFrame3.lean:58-63`）の 9 番目の conjunct が `ReadWorld cref`（`frameT_plus` が `hcell.2.2.2.2.2.2.2.2.1` として使っている）で、`ReadWorld.readKeeps`（BASE `Tools/ShippingStRefCorrespondence.lean:49`、証明済み）が `ReadKeeps cref` を返す。循環なし（`CellPrem` は `ReadKeeps` を使わない）。`h_C_EN4` と `h_C_RK1` は `FGLedgerPremisesStmt` で並ぶ closed Prop。→ 候補 A。 |
| C.RK-2 | `hHead : EnvFrame (coreHead X) mctx mref cctx cref`（成功 run の前後で `envAt cref` が等しい、per X / mctx / cctx） | U13 / U12b（g5rk-r23 `ReadKindsU12.lean`, `U13.lean:22`） | U | 読み: `coreHead`（BASE `Tools/ShippingEntryReadsLinked.lean:62-`）は `IO.getEnv "SPARKLE_PROFILE"`（`DRow.ioEnv`）、`IO.eprintln` / `flushStderr` / `IO.FS.Handle.mk` / `putStrLn` / `flush`（`Diag.profLog`）、`sparkle*` ref の get/set を含む。BASE の `envFrameEnd_framedA` は ioEnv を `¬ DRow` で除外し、`Diag` の経路は無い（R3 freeze §1 表 9 行）。U14 freeze §1 も「`hk` / `hHead` は run から払えない（run は return したと言うだけ）」。候補（L′ を前提とする）: `readsSupply_of_quiet`（par/rt-final `AccReads.lean`）は head の world w1 の `ReadsAt` を `coreHead_jqcA`（BASE `RunReads.lean` RR1）+ `QuietStrengthA` で出し `hHead` を使わない。ただし EN-1 前提。 |
| C.RK-4 | `hrun : RunsTo (readMachine declName allowGate) mctx mref cctx cref w r w'`、`hX : declName = X` | U13 / U12b / U11 / U10（g5rk-r23） | U（`hX` は R、`hrun` は D / U） | 読み: `hX` は定理が `declName` と `X` を別名で取るためで、利用側が `declName := X`、`hX := rfl` と置けば消える（U13 freeze もこれを gap に数えない、台帳 RK-4 の記述）。`hrun` は補助コマンド `readMachine`（`Tools/ShippingMachineCommand.lean:440`）の run の存在で、FG の仮説には無い。コンパイラ最終ゲート側の `RunReadsAt` の run からは出ない（別の `MetaM` コマンド）。データ供給（reader の被覆、DG-COVER / DG-READERTRACE 側）の義務で、供給元は見つからなかった。 |
| C.RK-6 | `hag : ReflExprAgree`（`∀ e, reflExpr e = reflExprS e`） | `storedFromRead_of_dataE_run` g5rk-r23 `ReadKindsU9.lean:96`、`body_readback` `Tools/Prototype/DGenStored2.lean:649`、FG 側の外側 binder `h_C_RK6`（BASE `ShippingGenFGLedgerPremises.lean:43`） | X | 読み: `reflExpr` は `partial def`（BASE `Tools/ShippingEntrySoundness.lean:1737`、`reflLevel` は `:1725`）で証明から不透明。`reflExprS` は構造再帰の写し（DGenStored2.lean:241）。DGenStored2.lean 自身が「evidence は `reflExpr_samples` の有限サンプルのみ、proof ではない」と明記。`partial` を構造再帰の `def` に置き換える（コンパイラ側の変更）か、等式を TRUSTED にするかのどちらかで、いずれも新しい前提・変更になる（要ユーザー判断）。 |
| C.RK-7 | U14 の `hM : ∀ e v1, RunsTo getEnv … w e v1 → envAt v1 = envAt w`、`hC : coreHead / getConstInfo / getEnv の 3 連の envAt 等式` | U14c `readMachine_agrees_runReads_of_ties`（設計のみ、Lean 無し）g5rk-r23 `scripts/gen5/DG_READKINDS_U14_FREEZE.md` §2 | U | 読み: U14 freeze は「Lean 未実装、`hk`/`hHead` の弱化で純減 0」と自己記述。`hM` は `getEnvFrame_of_readKeeps hk`（U14a、1 行）なので RK-1 → EN-4 に帰着、`hC` は `hHead`（RK-2）+ `envFrame_getConstInfo` で RK-2 に帰着。新しい payer は無い。置換の効果は scope の弱化だけで台帳の行は減らない。 |
| C.RK-8 | `hc : Complete cfg`、`hq : d.shape.body = quote …`、`hb : d.bposL = posB 0 (kindsOf d)`、`hv`、`hw : d.vwL = widV (kindsOf d)`、`hwf : d.packed.WF d.kb d.kv d.vw`、`hdom`（per d） | `readN_quote`、`readTot_of_quote_body`（g5rk-r23 `Tools/ShippingGen5ReadKinds.lean`）、`machine_wf_of_readN`、`packed_wf_cfg`（同 `:663-` 付近） | D（部分的に P） | 読み: `Complete cfg` は endpoint 構成 `kindsCfg dom (isExpr dom) ks` では既存定理 `kindsCfg_complete'`（g5rk-r23 `Tools/ShippingReaderKinds.lean:79`）と `isExpr_self`（`ShippingReaderComplete.lean:717`）で出る（`readN_expr_quote` U1e がその形）。`hwf` は `MachineData.ok`（BASE `Tools/ShippingMachineAuto.lean:217-242`）の conjunct `decide (d.packed.WF d.kb d.kv d.vw)` なので `d.ok = true`（T1L-32 の `DataOkB` に含まれる）から出る。`hq`・`hb`・`hv`・`hw`・`hdom` は package `d` のデータの性質（`bposL` が全 Bool binder の位置を並べた `posB` に等しい、等。`ok` の `∀ j<kb, binders[bpos j] = bool` は片方向で被覆でない）。`dataOfAt_sound`（g5do-r6 `Tools/ShippingGen5DataOf.lean:211`、DO-1）の 3 番目の conjunct が `hq` を与えるが `dataOfAt = some` の被覆が未供給。データ供給（sparkle-gen3-data-supply / DG-DATAOF / DG-COVER）の側。 |
| C.DO-2 | `Rdr`（実 reader との一致）と `s = sp`（Lean 命題無し） | g5do-r6 `scripts/gen5/DG_DATAOF_FREEZE.md` §11.3（定理なし） | X | 読み: §11.3 (a) `readMachine` との出力関係の定理が無い、(b) コンパイラの reader の同定が未了、(c) `tin = packTupleInputs entryV`、`fl = rootFloat` はいずれも `partial` で `machineShape?` が使う値との関係の producer が無い。C.RK-6 と同じく `partial def` が不透明という性質で、等式を立てるには compiler の `partial` の変更か TRUSTED が要る。Lean 命題がまだ無いので束縛変数ですらない。 |
| C.DO-3 | row 6a, C-CMP, C-QWIT, S-OK, S-COV-FLOAT, `dataOf at exprSize`（名前のみ） | g5do-r6 `scripts/gen5/DG_DATAOF_FREEZE.md` §4, §11.2, §11.4 | U（束ね行。S-OK は D、S-COV-FLOAT は DO-2 と同種で X） | 読み: §11.2 の表で 1,2,3,4,5,6,8 が「未供給 / 経路未発見」、7 は 4,5 に依存。C-QWIT は `hq : body = quote …` に対応するが run の供給元が無い（RK-8 と同じ）。S-OK = `d.ok = true`（DG-COVER / DG-WFCOVER）。Lean の statement が tree に無いので束縛変数として扱えない。 |

## 2. R / P の有望候補

### 候補 A: C.RK-1 を C.EN-4 の conjunct から消す（P）
* 消える ID: C.RK-1（`h_C_RK1 : ReadKeeps cref`）。
* 消える条件: reviewer が「`CellPrem` の `ReadWorld cref` conjunct を `ReadKeeps cref` の payer として使う」ことを受理する。`FGLedgerPremisesStmt` から `h_C_RK1` binder を除いた statement を新しい名前で立てる（旧定義・旧 Check は変えない）。
* 残る条件: C.EN-4（`CellPrem`、そのまま）、C.RK-2、C.RK-6、C.CV-4。
* root theorem の型案（Lean 風）:
  ```lean
  theorem readKeeps_of_cellPrem {Fresh : (σ : Type) → IO.Ref σ → Prop}
      {mref : ST.Ref IO.RealWorld Meta.State} {cref : ST.Ref IO.RealWorld Core.State}
      (h : Tools.ShippingGen5EnvFrame3.CellPrem Fresh mref cref) :
      Tools.ShippingStRefCorrespondence.ReadKeeps cref :=
    h.2.2.2.2.2.2.2.2.1.readKeeps
  -- FGLedgerPremisesStmt' := FGLedgerPremisesStmt から (h_C_RK1 : ReadKeeps cref) を除く
  ```
  conjunct の位置（`.2` を 8 回して `.1`）は `frameT_plus` の `hcell.2.2.2.2.2.2.2.2.1`（BASE `EnvFrame3.lean`）と同じ。
* 費用（見込み、測っていない）: lemma 5 行、statement の複製 40 行、Check（型一致、BINDERS = 旧 − `h_C_RK1`、mutant 数本）100 行前後。
* 確かさ: 高い（lemma は 1 行の合成、読みでは型が合う）。Lean 未確認。
* 新しい freeze / TRUSTED: freeze は要る（新 statement と Check を足すため、HORD_RUN と同じ型の文書）。TRUSTED / law / compiler 変更は要らない。
* 新しく増える行: なし（C.EN-4 は既存の行）。
* 台帳への効果（見込み）: FG の非リーフ −1（TY-O の 1 行）。リーフ不動。g5rk-r23 の U13 系（BASE に無い）で `hk` を取る定理の binder 自体は変わらず、利用側が `readKeeps_of_cellPrem` を通す。
* 注意: これは「束縛変数が既存の行に置き換わる」型（A.P-24 型）だが、置換先の C.EN-4 自体が TRUSTED かどうか未決で、RK-1 だけが先に消える。C.EN-4 の決定が「採用しない」になれば RK-1 の payer も無くなる。

### 候補 B: C.EN-3 を depth 0 の根で不要にする（R、条件付き）
* 消える ID: C.EN-3（`hC` / `hE` / `hN`）。
* 消える条件: depth 0 の根では cache 半分を使わない版の `closingRun0` を L′ 上で使う。`closingShared_of_run` は `hw.1`（JQ）しか使わず、`coreHead_invAt0` の D = 0 分岐も `hw.1` のみ（BASE `ClosingRun.lean:97`）。`head_jqc_start`（`EnvQ.lean` Q10）は既にこの形（`Start L` と `hq` `hA'` から `JQC L'.O 1 w1`）。
* 残る条件: EN-1（`hq`）、EN-2（`hd`、`hA'`）、EN-4、EN-5。これらが無いと L′ 自体が無い。したがって候補 B 単独では L′ 経路の前進にならず、EN 系の行数が 1 減るだけ。EN 系が最終的に採用されないなら意味がない。
* root theorem の型案:
  ```lean
  theorem closingRun0_of_runR_jq
      (L L' : Laws mref cref) (hq : QuietStrength L L' (envAt cref w)) (hd : AdmDown L L')
      (hA' : AdmCtx L'.O.quiet mctx cctx) (hjq : JQ L'.O.quiet 0 w) (hd0 : dv w = 0)
      ... -- closingRun0_of_runR の hs : Start L mctx cctx w を hjq（JQ のみ）に置換
      : ClosingRun0JQ L' P Reach mctx cctx X p Gen w w' raw D  -- start0 を JQ 形に置換
  ```
  `ClosingRun0` は結論に `Start L …` を持つため別 structure が要る。
* 費用（見込み）: `closingShared_of_runR` は D = 0 の枝で `hw.1` と `hc'` しか使わないはずなので、仮説だけを JQ 形に替えた複製で 60〜100 行、Check 100 行前後。
* 確かさ: 中（型の読みのみ。`invAt_w5_of_runReadsAt_JQC`（`ClosingRun2.lean:48`）が `hw : JQC` を後段で使っていないか、再確認が要る）。
* 新しい freeze / TRUSTED: freeze 要、TRUSTED 不要。
* 新しく増える行: なし。
* 効果: FG 非リーフ −1（EN-3）の見込み。ただし EN 系全体が未払いのまま 1 行だけ減る形なので、台帳上の「実質」の前進かは reviewer 判断（EN-1/2 が未供給なら、`Start L′` を使わない根を作っただけ）。推奨度は A より低い。

### 候補にならなかったもの（理由）
* C.EN-6 / C.RK-2 / C.RK-7: depth 0 の根だけなら `ChainReadsAt (envAt cref w)` は `readsAt_self` + `hk` + `hHead` から出る（g5rk-r23 `readsAt_chain_of_head`）。しかし `T1HypND.defines`（全 world）を `MachineDefinesR` にするのは T1 の共有定義の変更、depth ≥ 1 は L′ が要る。新しい前提を足すので X。
* C.CR-2: `genP_generated` 経路は `GenSFacts K`（DG-FACTS）と `K : AssignKit` と `ReadsSupplyAt` を足す。束縛変数の置換ではなく移動。
* C.CR-4: 束縛変数は残る。数え方の判断（LEDGER_CROSSCOUNT_DECISION 案 B の拡張）で、Lean の進捗ではない。

## 3. 読んだもの
BASE: `Tools/ShippingGen5{Env,EnvR,EnvQ,EnvStart,EnvCache,EnvCacheC,EnvCacheD,EnvCacheE,EnvFrame3,RunReads,ClosingRun,ClosingRun2,FG,T1ND}.lean`、`Tools/ShippingGenFGLedgerPremises.lean`、`Tools/ShippingGen2Defs.lean:46-330`、`Tools/ShippingChildInvA.lean:263-334`、`Tools/ShippingChildCacheA.lean:105-121`、`Tools/ShippingStRefCorrespondence.lean`、`Tools/ShippingEnvSnapshot.lean`、`Tools/ShippingEntryReadsLinked.lean:55-100`、`Tools/ShippingMachineAuto.lean:170-260`、`scripts/gen5/{HORD_RUN_FREEZE,LEDGER_CROSSCOUNT_DECISION,DG_ENV_T2_FREEZE_R3}.md`。
他 branch: g5rk-r23 の `ReadKindsU9/U12/U13`、`ShippingGen5ReadKinds.lean`、`DGenStored2.lean`、`DG_READKINDS_U14_FREEZE.md`; g5ac-r27 の `AccGenP.lean`、`Acc.lean`; par/rt-final の `AccReads.lean`; g5do-r6 の `DG_DATAOF_FREEZE.md` §11; FG 台帳 `par/fg-ledger-sync:scripts/gen2/premise_ledger/C_M5dg.md`。
確認していないもの: Lean での型検査（build 成果物が無い）、`DG_ENV_FREEZE.md` §4 の A/B/C 決定の記録（par/gen5-t2 側、見つからなかった）。

---

## 担当 4

### out_4: C.SM-1,6,7 / C.AC-4,5,7,9 / C.CV-4,5,6 / C.DG-1 / D.D-1,3,4,5,7,8（17 行）の出口調査

担当 N=4。読み取りのみ。Lean は実行していない（下の「確認」は 0 件。すべて「読み」）。mutant の話は出てこない。「見つからなかった」は「この調査では供給元・経路が見つからなかった」の意味。台帳の行の数・文は変えない。

## 0. 読んだ tree と前提

* 行の原文: `par/fg-ledger-sync` の `scripts/gen2/premise_ledger/{C_M5dg,D_M5t2}.md`、PREMISE_LEDGER.md §8.x/§12。
* DG 系の Lean は **`par/rt-admit-decision` aab355f2**（= `par/rt-final` 378f8e31 + 文書 1 件、Tools/ShippingGen5*.lean 105 本）を `git archive` して scratchpad の `rad/` で読んだ。個々の定理の元の承認 SHA は台帳どおり（Cover* = kjob/g5cv-r13@44d72eaf、Sem* = kjob/g5sm-u23@7af6c7cc、Acc* = kjob/g5ac-r26@cff12a48 と ckit2、DataOf* = kjob/g5do-r6@063056d6、ReaderTraceFinal = par/rt-final@378f8e31）。
* DC 系（FG.lean, DeclConnect.lean, DCEntry{,D,N,R,S,T,W}.lean, ShippingGenFGLedgerPremises.lean）は base 392dc221 で読んだ。`DCEntryU.lean`（`noRawBelow_of_coreRun`）は `kjob/g5dc-r23`@74343ad8 だけにある（未レビュー・clean build 未）。
* **統合 tree が無い（全 branch を調べた）**: (ReaderTraceFinal または GDCover1) と (ClosingRun2) と (DeclConnect) と (SemGenData) を同時に含む branch は 1 つも無かった。base 392dc221（ClosingRun3/4 を持つ）には Sem/Acc/Cover/DataOf/ReaderTrace が 1 本も無い。したがって下の候補はどれも「統合 tree を作る」費用が別にかかる（各候補の費用には含めていない）。
* 参照資料: GENDATA_COVER_SURVEY.md / GENDATA_ROADMAP.md（kjob/gdrm2 7c223331）、GDCOVER01_RESULT.md、GD_W3_WITNESS.md、RT_FINAL_FREEZE.md、RT_ADMIT_DECISION.md（aab355f2）、DG_COVER_FREEZE_REV4..7、DG_READERTRACE_FREEZE_REV14。

### 0.1 C.CV-5 の「reader state `st` は run-local」の確認（依頼された点）

`Tools/ShippingGen5ReaderTraceFinal.lean:10`（par/rt-final@378f8e31）`readerTrace_final` の型（要点）:

```lean
theorem readerTrace_final (hE hla hi1 hr hh hbt hEq : …) (env : Lean.Environment) (hK hC hD hv hbr hraw hnode hrr : …)
    (hfb : FuelBridge)                                   -- = C.CV-4
    {ci0 E : ConstantInfo} (hci : CiDirect env ci0) (hbranch : E = ci0 ∨ E = inlinedConst (userInliner env) ci0)
    {dd : DefinitionVal} (hEd : E = ConstantInfo.defnInfo dd)
    {sp : MachineShape} (h : machineShape? false [] E (structEnv env) = some sp)
    {lvl : Lean.Expr → Nat} {d : MachineData} (hd : dataOfAt lvl E (structEnv env) sp = some d) :
    (∀ n, TraceGood (structEnv env) (nDeclOfCi E) (readF (structEnv env) n)) ∧
    ∃ (n : Nat) (p : ShapePre) (en : Lean.Expr) (st0 : MachRead) (env' : List MachVal) (st1 st : MachRead) (v : Lean.Expr),
      StateSideWitness E (structEnv env) sp n p en st0 env' st1 st v ∧
      FReachC (nDeclOfCi E) {} st0 ∧ FReachC (nDeclOfCi E) st0 st1 ∧ FReachC (nDeclOfCi E) st1 st ∧
      TrInv (structEnv env) (nDeclOfCi E) st ∧ ShapeAgree d st ∧ FullInv (kDOf d) st ∧ LetsNoLoose st
```

* `st : MachRead` は **束縛変数（仮説）ではなく結論の `∃` 変数**。仮説側に `st` は 1 度も現れない。C.CV-5 の `hsp hss hls hn` は `shapeAgree_of_sides` の引数で、`readerTrace_final` の中では `dims_of_dataOfAt hd`（U2Compose.lean:52、`dataOfFrom_dims` DataOfDims.lean:108 経由）と `StateSideWitness` の最後の 4 節（`sp.insts = st.insts.toList ∧ …`）から出ていて、仮説には残らない（読み: ReaderTraceFinal.lean の証明本体）。
* `st` の出どころは `hfb`（C.CV-4）から取った燃料 `n` と `machineShapeF_state_side`（Cover5.lean:55）で、`machineShapeF n false [] E senv true`（全域な fuel 版）の実行状態。**pure 関数であって run の状態ではない**。一意性は `stateSide_functional`（ReaderTraceSameSt.lean:18）。
* run との接点は `h : machineShape? … = some sp` だけで、これは `RunReadsAt.shapeEq`（RunReads.lean の structure の最後のフィールド）の形そのもの。run → `h` の継ぎ目: `RunReadsAt.chain` の `ci`（getConstInfo の結果）、`envR`/`envR'`、`RunReadsAt.shapeEq : machineShape? false [] (entryConst true false [] ci (instancePredicate envR) (userInliner envR) (structEnv envR)) (structEnv envR') = some shape`。`readerTrace_final` は単一の `env` を取るので `envR = envR' = env₀` が要る。その材料は `ReadsAt env₀ cref w`（Env.lean:29、`envR_of_readsAt` で `structEnv`/`userInliner`/`instancePredicate` の一致、`ci_of_readsAt` で `env₀.find? X = some ci`）で、供給は AC-7 `ReadsSupplyAt`（= C.EN-1 + RK-1）。`hbranch` は `entryConst` の定義（Elab.lean:5277、`inlinedConst inl ci` か `ci` の `if`）の場合分けで出る。`hEd` は `peel_of_machineShape`（GDCover0.lean:71、結論に `E = .defnInfo d` を含む）で出る。`hci : CiDirect env ci0` は `env₀.find? X = some ci` そのもの。（読み）
* したがって「`st` が run-local だから行が動かせない」という台帳の注記は、`ShapeAgree d st` / `LetQuoteEqC d st`（GDW3.lean:163 `letQuoteEqC_witness`）/ `FullInv` / `LetsNoLoose` については当てはまらない。同じ `st` が G1 の `StateSideWitness` の `st` として全部に共通（GDCover1.lean:58 `shapeAgree_witness`、GDW3.lean:146）。run に残る依存は `h`（= `shapeEq`）と、環境一致 `ReadsAt env₀`（AC-7/C.EN）。

## 1. 行ごとの表

分類: R/P/D/U/X はブリーフの定義。「確かさ」は 高/中/低（読みの確からしさ）。SHA 表記の `@rad` は `par/rt-admit-decision`@aab355f2 を指す。

| ID | 束縛変数(名:型の要点) | FG定理 file:line @branch:SHA | 分類 | 根拠・読み/確認 |
|---|---|---|---|---|
| C.SM-1 | `hs : DataOfSound dataOf initsOf`（`∀ E senv s d, dataOf E senv s = some d → d.shape = s ∧ d.ok ∧ d.shape.body = quote … d.packed ∧ d.initOk (initsOf d) = true`、SemGenData.lean:18）＋被覆 `dataOf E senv s = some d` | `GenData.toIn` SemGenData.lean:34、`hunf_of_genData` :62、`factsOf_all_of_genDataInv` :77、`factsOf_genS_assembled''` AccGenDataKit.lean:41、`hinv_genS` AccHinv.lean:18、`factsOf_genS_assembled` AccSemJoin.lean:36 @rad（元 kjob/g5sm-u23@7af6c7cc, kjob/g5ac-r26@cff12a48） | **P（hs の健全性半分）／U（被覆半分）** | 読み: `dataOfAt_sound`（DataOf.lean:211、承認済み）の結論は `DataOfSound` の本体と同じ 4 連言で、`initsOf` は DataOfPure.lean:354 の具体 `def initsOf (d : MachineData) : HList (tys d.ss)`（型は SemGenData.lean:19 の引数と同じ形）。よって `dataOf := fun E se s => dataOfAt lvl E se s`, `initsOf := Tools.ShippingGen5DataOfPure.initsOf` と固定すれば `hs := fun E se s d h => dataOfAt_sound lvl h`（1 行）。`factsOf_genS_assembled''` は `hs` と `genData₀` だけを取る（hinv/hunf/hacc は中で `hinv_genS` が処理済み）。被覆（`dataOfAt = some d`）は `dataOfAt_sound` が作らない（DataOf.lean ヘッダの "What is NOT here"、台帳 §11.3）。被覆は ReachCover の (D) 連言（C.AC-4）と同じ義務。台帳 §8.1 は C.DO-1/C.AC-1 を C.SM-1 に merged 済み。|
| C.SM-6 | `wf : GenWF d = true`（`GenData` のフィールド SemGenData.lean:27、`GenIn.wf` SemGen.lean:61）。`GenWF d = RowA d && RowB d && RowC d`（SemGen.lean:58）= `GenWFRows` の 7 連言 a1 a2 a3 a4 b1 b23 c（Cover.lean:92） | `genWF_of_rows` Cover.lean:104、`rowA2_of_inv` Cover3.lean:762、`rowA3_of_inv` :768、`rowA4B23_mem_of_inv` :776、`rowB1_of_inv` :798、`rowC_of_reader_canon` Cover3Canon.lean:193、`rowC_of_reader_ok` Cover4.lean:54 @rad（元 kjob/g5cv-r13@44d72eaf） | **U**（7 連言のうち 6 は R 候補。残り 1 つ B3 の供給元・経路が見つからなかった） | 読み: a1 = `ShapeAgree.nIn`（shapeAgree_witness の d 側 `hn`）。a2/a3/a4/b1/c は `readerTrace_final` の結論 `ShapeAgree d st`, `FullInv (kDOf d) st`, `LetsNoLoose st` と `letQuoteEqC_witness`（GDW3.lean:163）と `rowC_of_reader_ok` の `d.ok`（`dataOfAt_sound` .2.1）から。b1 の `hcb` は C.CV-6 の候補（下）。**b23 の `letSort d l0 = some (.bits aw) ∧ letSort d l1 = some (.bits dw) ∧ letSort d l2 = some .bool ∧ letSort d l3 = some (.bits aw)`（B3 = memory arg sorts）は `rowA4B23_mem_of_inv` が出さない**（DG_COVER_FREEZE_REV4.md:202,216 / REV5.md:34）。供給元は T1 台帳の T1L-66 `MemSrcKinds for a real run`（t1led §、`sparkle-gen3-src-argw`、状態 unknown）。`letSort d l = (d.ls[l]?).map (·.1)`（SemGen.lean:23）を T1L-66/T1L-47 の `ReadTypedAt` に結ぶ補題はこの調査では見つからなかった。W6（`genWF_of_prod`）は GENDATA_ROADMAP §3/§4 に型案のみ、Lean 無し。|
| C.SM-7 | `hord : (originOf p.d k).child? = none`（`genExtAtCall_of_genSem`、SemExtPkg.lean:17-21） | `genExtAtCall_of_genSem` ShippingGen5SemExtPkg.lean:17 @rad（kjob/g5sm-u23@7af6c7cc）。使用側: `h_D_T1` in ShippingGenFGLedgerPremises.lean:55-58 @base 392dc221（antecedent に同じ guard を持つ）、`GenExtAtCall` T2Tie.lean:238 | **P** | 読み: `originOf d k := d.shape.instOrigins.getD k .ord`（SemGen.lean:24、定義そのもの）。`h_D_T1` の内側の前件が `(p.d.shape.instOrigins.getD k .ord).child? = none →` で、`TgtRun.call` の `ord`（FG.lean）も `CallEdge`（Acc.lean:66-68）も同じ `child? = none` を持つ。`genExtAtCall_of_genSem … (hord := ‹antecedent›)` が `rfl` で通る。k が `ordCallees₀` に入る形でも `ordCallees₀_mem`（AccOrdCallees.lean:21）が同値を与える。run の事実も `instFields = []` の場合分けも要らない。確かさ 高。ledger の注記 `[PA]` と一致。|
| C.AC-4 | `ReachCover K Reach := ∀ c, Reach c → ∃ E g, entry₀ env₀ c = some E ∧ K.genData₀ E = some g`（Acc.lean:206）と `hcl : ∀ X c, Reach X → CallEdge K X c → Reach c`。K/Reach の carrier 未固定 | `genS_isSome_of_cover` Acc.lean:210、`machineRouteAt_of_cover` AccRoute.lean:49、`accServed0_of_cover_gates` :70、`accServed0_of_cover` AccServed.lean:445、`genP_pkg` AccGenP.lean（GenPPkgStmt）@rad（kjob/ckit2@4bc671dd, kjob/g5ac-r26@cff12a48） | **U**（`hcl` は P、ReachCover の (S) は R 候補、(D) は U、(W) = C.SM-6） | 読み: carrier は固定できる。`K := mkKit dataOf (GenData dataOf · (structEnv env₀)) (·.d) (genDataC dataOf env₀) ordCallees₀ …`（GDCover0.lean:36 `reachCover_iff_sdw` が `hev := genData_gdEvidence`（AccGenDataKit.lean:11）で ReachCover を (S)(D)(W) に分解済み）、`Reach := ReachEdge K Top`（Acc.lean:201）。すると **`hcl` は `ReachEdge.edge` のコンストラクタで成立（P）**。(S) `machineShape? false [] E (structEnv env₀) = some sp` は `RunReadsAt.shapeEq`＋`ReadsAt env₀`（R 候補。ただし callee の `c ∈ Reach` ごとに core run が要る。静的な `CallEdge` 到達と run の対応は Lean で見つからなかった）。(D) は GENDATA_ROADMAP の G3(D3)/G4(D1)/G5/G6/G8/G9、GDCOVER01 / GDCover2 までで条件 1(`peel_of_machineShape`, GDCover0.lean:71) と条件 2(`dataOfFront_len_of_production`, GDCover2.lean:76) のみ前進。条件 3(dom 一致: D1/D3 の判断待ち)、4 (C-QWIT)、8 (S-OK) は経路が見つからなかった。|
| C.AC-5 | `GatesNoneAt env₀ Reach := ∀ c ci, Reach c → env₀.find? c = some ci → certifiedShape? false [] (entryConst …env₀…) = none ∧ mixedCertifiedShape? … = none`（AccRoute.lean:34） | `machineRouteAt_of_cover` AccRoute.lean:49、`accServed0_of_cover_gates` :70、`gatesNoneAt_of_gateRunsAt` AccGates.lean:~38、`gatesNoneAt_of_readerRuns` AccReader.lean:~58 @rad（kjob/g5ac-r26@cff12a48） | **U**（R 候補あり） | 読み: `RunReadsAt.gates`（RunReads.lean の structure フィールド）が実 run の 2 gate refusal を `envR` で与える。`GateRunsAt`（AccGates.lean）は RunReadsAt の chain（getEnv/getConstInfo の run）と `ReadsAt env₀`（AC-7）から組める形だが、`runReads → GateRunsAt` の継ぎ補題は Lean に無い。`gatesNoneAt_of_readerRuns` は `readMachine c false` の run（generator 側）を取るので production run の道とは別。さらに `∀ c ∈ Reach` に対して run が要る（AC-4 の (S) と同じ穴）。T1 側の `T1Hyp.defines`（A.P-06 の closure）経由は `MachineDefines` が全 world 量化（ShippingMachineEntry.lean:2345）なので論理的には gate 事実を含むが、`MachineDefines → GatesNoneAt env₀` の補題は見つからなかった。|
| C.AC-7 | `ReadsSupplyAt e L Reach := ∀ X, Reach X → ∀ mctx cctx w, AdmCtx → JQC L.O (dv w) w → ChainReadsAt e …`（AccReads.lean:49） | `accServed0_of_cover_gates` AccRoute.lean:70、`readsSupply_of_quiet` AccReads.lean:99 @rad（kjob/g5ac-r26@cff12a48） | **P**（条件付き） | 読み: `readsSupply_of_quiet {L L'} {e} (hq : QuietStrengthA L L' e) (hg : ∀ mctx cctx, GetEnvFrame mctx mref cctx cref) (Reach) : ReadsSupplyAt e L' Reach`（証明済み、AccReads.lean:99-108）。`QuietStrengthA` は EnvQ の `QuietStrength`（C.EN-1 `hq`）と同文（AccReads.lean:31 のコメント）。`GetEnvFrame` は C.RK-1 `hk : ReadKeeps cref` から `getEnvFrame_of_readKeeps`（StRefCorrespondence.lean:75、証明済み）。よって AC-7 は **既存行 C.EN-1 と C.RK-1** に置き換わる。条件: ルート定理を `L := L'`（強化された法則）で述べること（`readsSupply_of_quiet` の結論は `ReadsSupplyAt e L' Reach`）。これは EN-1 を使う他の箇所（`t1HypND_up` 等）と同じ形で、新しい行は増えない。|
| C.AC-9 | `RunDataLink L Reach := ∀ c ∈ Reach, ∀ mctx cctx, AdmCtx → ∀ shape, MachineDefinesR … c shape → ∃ d, dataOf₀ K c = some d ∧ d.shape = shape`、`hDS : DataOfShape K := ∀ E se s d, K.dataOf E se s = some d → d.shape = s`（AccServed.lean:64-70） | `accServed0_of_route` AccServed.lean:431（`RunDataLink`）、`accServed0_of_cover` :445 と `accServed0_of_cover_gates` AccRoute.lean:70（`hDS`）、`dataOfShape_of_sound` AccDataSound.lean:30、`mkKit_dataSound` AccMkKit.lean:74 @rad | **P** | 読み: cover ルート（`accServed0_of_cover_gates`）は `RunDataLink` を取らず `hDS : DataOfShape K` だけを取る。`DataOfShape K` は `DataSound K`（AccDataSound.lean:23）の第 1 連言（`dataOfShape_of_sound`、証明済み）。`DataSound K` は `mkKit_dataSound … (hf : DataSoundAt f)`（AccMkKit.lean:74）から、`hf` は `f := dataOfAt lvl` なら `fun E se s d h => (dataOfAt_sound lvl h)` の先頭 3 連言（C.SM-1 と同じ carrier 固定）。`RunDataLink` はこの道では使わないので行ごと不要。`hev hloc hdecl hd` は `genData_gdEvidence`, `genData_genSem_local/decl/d`（AccGenDataKit.lean:11-30）で GenData carrier では P（C.AC-2/AC-3 の側。この表の対象外）。確かさ 高。|
| C.CV-4 | `hbr : ShapeFuelBridge := ∀ E senv sp, machineShape? false [] E senv = some sp → ∃ n, machineShapeF n false [] E senv true = some (some sp)`（Cover5.lean:97-100、`FuelBridge` U2Compose.lean:30、`hfb` in readerTrace_final） | `shapeAgree_of_production` Cover5.lean:97、`stateSide_of_production` GDCover1.lean:29、`readerTrace_final` ReaderTraceFinal.lean:10、`h_C_CV4` ShippingGenFGLedgerPremises.lean:~45 @rad／base（T1L-43 `OSH` と同一前提） | **X** | 読み: `machineShape?` は `partial` な reader（`machNorm`, `packTupleInputs`, `readF` 系 7 本）を呼び、kernel に等式が無い（`docs/parallel/B-readerinv.md` §8 の記録: 「R1, LenOk of the returned state and P5 are facts about partial / opaque constants with no kernel equations … unless the readers are made non-partial in the compiler (a user decision)」。ShippingMachineShapeTail.lean ヘッダ）。GENDATA_ROADMAP §1 の調査 B（e1127abe）: `machNorm` と reader 7 件は測度でも `partial_fixpoint` でも通らない。全域化はコンパイラ変更で、ユーザー判断（M5 Risk）。`readerTrace_final` も `hfb` を仮説に残し、RT_ADMIT_DECISION §2 が「既存の行（変化なし）」と明記。T1L-43 と共有なので二重計上なし。run から `∃ n` を出す経路は見つからなかった。|
| C.CV-5 | `hsp : d.shape = sp`, `hss : d.ss.length = sp.layout.slots.length`, `hls : d.ls.length = sp.layout.lets`, `hn : sp.insts.length ≤ d.nIn`, `hs`（4 連言 `sp.insts = st.insts.toList ∧ …`）。`st` は §0.1 のとおり結論の ∃ | `shapeAgree_of_sides` Cover5.lean:76、`shapeAgree_of_fuel_run` :87、`shapeAgree_of_production` :97（元 kjob/g5cv-r13@44d72eaf）。消す側: `shapeAgree_witness` GDCover1.lean:58、`shapeAgree_witness_from` :41、`dataOfFrom_dims` DataOfDims.lean:108、`dataOfAt_dims`、`readerTrace_final` @rad | **P**（条件付き） | 読み: `shapeAgree_witness (hbr) (h : machineShape? … = some sp) (hd : dataOfAt lvl E senv sp = some d) : ∃ n p en st0 env st1 st v, StateSideWitness … ∧ ShapeAgree d st` が `hsp hss hls hn hs` を全部 `dataOfAt_dims`＋witness の末尾 4 節から作る（GDCover1.lean:58-66、Pod target build OK の記録: GDCOVER01_RESULT.md、clean build は coder）。置換先は既存行 **C.CV-4（hbr）＋ hd**。`hd` は `GenData.hdata : dataOf E senv d.shape = some d`（SemGenData.lean:27）で `dataOf := dataOfAt lvl`（C.SM-1/AC-9 の carrier 固定）の下では structure のフィールドから出るので、新しい行ではない。GDCOVER01_RESULT.md の確認 (a)(d) は一致、(b) は「`d` が `dataOfAt … = some d` を満たす場合に限る」、(c) carrier = `dataOfAt lvl` に固定されていることが条件、(e) C.DO-3 の 6a/6b との台帳記述の食い違いは台帳側の訂正（reviewer）。循環なし（CV-4 は CV-5 に依存しない）。|
| C.CV-6 | `hcb : ∀ k (hk : k < d.shape.insts.length), (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2`（`rowB1_of_inv` Cover3.lean:798）、R-in、R-dom（名前のみ） | `rowB1_of_inv` Cover3.lean:798、`callKind_eq_inst` Cover.lean:~249 @rad。供給側: `machineShape?_callBinder` ShippingMachineShapeTail.lean:61（base 392dc221 に在り、build 済み）、`dataOfFrom_nIn` DataOfDims.lean:98、`readerTrace_final` | **R**（`hcb` は 25 行程度の新補題で、R-in/R-dom は readerTrace_final 経由。後者は RT_ADMIT_DECISION の (A) が条件） | 読み: **(hcb)** `machineShape?_callBinder h : ∃ bs e, mixedGatePeel (packTupleInputs d.value) = some (bs, e) ∧ ∀ k < sp.insts.length, (sp.binders.map (·.2))[bs.length + k]? = (sp.insts.map (·.2.2))[k]?`（証明済み、`ShapeDecomp.callBinder_bs` 経由）。`dataOfFrom_nIn` は同じ peel `p` と `d.nIn = p.1.length + s.insts.length` を与え、`kDOf d = p.1.length`（`kDOf_eq_nDeclOfCi_of_dataOfFrom` ReaderTraceKDOf.lean:15 が同じ手筋で証明済み）。peel の一意性で `bs.length = kDOf d`。`d.shape = sp` は `dataOfFrom_dims`。`List.getElem?_map` で `hcb` に直せる。**REV4 §2(DG_COVER_FREEZE_REV4.md:202) は `hcb` を `ShapeDecomp.callBinder_bs` 型の binder fact と書く。台帳 C.CV-6 の「`hcb` は 4246 note の B3 = src-argw」は、B3 = b23 の letSort 4 等式（C.SM-6 の残り）との取り違えに見える**（REV4.md:214 は B1→`hcb`、:216 は B3→src-argw と別行）。(R-in/R-dom) `readerTrace_final` の `ShapeInputs'`（hv hbr hraw hnode hrr … から）と `TrInv`（`DomPh`、Shape2.lean が `DomAtomic dom` を外した版）で供給済み（確認ではなく読み）。READERTRACE_FREEZE_REV14.md:213 が「R-in/R-dom の部分のみ。`hcb` は覆わない」と書いたのは、その時点で `hcb` の経路を見ていなかったため。|
| C.DG-1 | (i) `dataOf` 成功、(ii) `GenWF d = true`、(iii) `P = genP env₀` と `X ∈ dom`。`GeneratedAt` は DGEN_FREEZE の設計文 | 設計: DGEN_FREEZE.md @par/gen5-t2:c398021c。Lean 側の対応物: `GeneratedAtK`, `genP`, `genP_generated`, `genP_pkg`, `factsOf_genS_assembled''` AccGenP.lean / AccGenDataKit.lean:41 @rad（kjob/g5ac-r26@cff12a48, ac6v-a88c3e9c clean build 記録あり） | **P**（条件付き。C.AC-4 と C.DG-1(iii)=D.D-3 に帰着） | 読み: GENDATA_COVER_SURVEY §1.1 が「(i)(ii) は C.AC-4/C.SM-6 と別の義務ではなく同じ義務の run 側の言い方」と書く。Lean では `genP_pkg : GenPPkgStmt`（`GenSFacts K` と `hcl hacc hcov hOk` を取り `∀ c ∈ Reach, ∃ q, genP K hF c = some q ∧ q.decl = c ∧ DataOk q`）が (iii)＋「X∈dom」を与え、`genP_generated` が `GeneratedAtK` を与える（どちらも証明済み）。`hF : GenSFacts K` は `factsOf_genS_assembled'' hs genData₀`（hs だけ）。`hcov`=C.AC-4、`hacc`=C.AC-8、`hOk`=A.P-20(DataOk)。つまり C.DG-1 の内容は既存行の組に Lean で置き換わる。但し「行の統合の数え方」は reviewer 判断（要ユーザー判断）で、(i)(ii) が C.AC-4/C.SM-6 の言い換えという台帳 §11.3 の見方に依る。C.CR-2 `hGen` への接続（`Gen ci envR envR'` を `GeneratedAtK` に結ぶ）は別行で、この調査では見ていない。確かさ 中。|
| D.D-1 | carrier `ReflectsAll : Laws mref cref → Name → List (String × Nat) → Prop`（FG.lean:30,42,54）。EntryWitness の第 3 conjunct | `EntryWitness` FG.lean:30、`FG_COND`/`FG_CONNECT` FG.lean:42/54、`entryWitness_postEntry` DCEntryW.lean:19、`FGLedgerPremisesStmt` ShippingGenFGLedgerPremises.lean:~30 @base 392dc221 | **X** | 読み: ShippingGenFGLedgerPremises.lean ヘッダが「carriers `ReflectsAll` `Post` `GP` `CV` are universally quantified BOOKKEEPING binders only」と明記。定義を与えること自体が FG の scope を決める新しい文で、台帳の注記どおり per-route rows B.G-*/B.F-4/B.P-*/A.P-06… の束にしかならない（束ねても行は減らない）。`ReflectsAll = False` 型の scope 縮小は不採用（seq3553）。定義を探したが Lean 側に無い。要ユーザー判断（定義の選択）。|
| D.D-3 | carrier `GP : Environment → Pkgs ι dom`（FG.lean:42）。merged D.P1, D.T-7 | `FG_COND`/`FG_CONNECT` FG.lean:42/54、`nv_gp`、`genP_pkg`/`genP_closed`/`genP_d_edges` AccGenP.lean、`factsOf_genS_assembled''` AccGenDataKit.lean:41 @rad／base | **P**（条件付き・要ユーザー判断） | 読み: `GP := fun env => genP (K env) (hF env)`（`K env := mkKit dataOf … (genDataC dataOf env) ordCallees₀ …`、`hF env := factsOf_genS_assembled'' hs (genDataC dataOf env)`、`hs` は env 非依存なので `GP` は全関数として書ける）。このとき FG の `GP (envAt cref w) declName = some p`（O2）は `genP_pkg` に帰着し、前件は `hcov`(C.AC-4)・`hacc`(C.AC-8)・`hcl`(定義)・`hOk`(A.P-20) で、全て既存行。`hs` は C.SM-1。**ただし GP を `genP` に固定することは、FG 結論を DGEN 経路の packages に限る選択**（台帳 D.D-3 のコメントの「FG-REF」）で、reviewer／ユーザーの承認が要る可能性がある。統合 tree（Acc/Sem と DC を同居させる）が前提。確かさ 中-低。|
| D.D-4 | carrier `CV : ConstValueRel := Environment → Name → (α : Type) → α → Prop`（DeclConnect.lean:267）と `ConstValueFunctional CV`（FG.lean:12、結論の第 1 conjunct） | `FG_CONNECT` FG.lean:54、`declConnect_of_rows` DeclConnect.lean:300、`dcImp_of_dcGen` DeclConnectAbs.lean @base 392dc221 | **U** | 読み: DeclConnect.lean:12,266 が「`ConstValue` の定義は無く、`ConstValueRel` は型だけ（inductive `ConstValueE` は DCF unit のもので未記述）」。全 branch で `def ConstValue` / `inductive ConstValue` を探したが見つからなかった。`ConstValueFunctional` は CV の構成から出る形を想定しているが、構成が無い。decl-bridge（todo のみ）が供給予定。|
| D.D-5 | `hAcc : ∀ X, Tgt X → Acc R X`、`hclosed : ∀ X c, Tgt X → R c X → Tgt c`、`hstep : ∀ X, Tgt X → (∀ c, R c X → Tgt c → DeclConnectAt CV env₀ P c) → DeclConnectAt CV env₀ P X`、順序 `R`（`declConnect_of_rows`） | `declConnect_of_rows` DeclConnect.lean:300 @base 392dc221（kjob/g5dc-r21..r23@0fcce4e7）、`TgtRun` FG.lean:19 | **U**（`hclosed` は R、`hAcc` は P(C.AC-8)、`hstep` は U） | 読み: `R c X := ∃ q, P X = some q ∧ ∃ k hk, (q.d.shape.instOrigins.getD k .ord).child? = none ∧ (q.d.shape.insts[k]).1 = c` と取れば、`hclosed` は `TgtRun.call`（FG.lean:19-22）そのもの（R）。`hAcc` は `Acc (CallRel K)` の `Subrelation` で、`genP_d_edges`（AccGenP.lean）が `R c X → CallRel K c X` を与え、`Acc (CallRel K) X` は `hacc_of_top_runs`（AccReads.lean:137、C.AC-8）の結論（`TgtRun P declName ⊆ ReachEdge K {declName}` を帰納で示す補題は見つからなかった。短いはず）。`hstep` は台帳の注記どおり rows 0-4（値の存在、本体の unfold、shape/body、quote/eval の一致、`src = obs (stateLoop …)`、calls）で、DeclConnect.lean の `ShapeMatches`/`CV` を含む義務。経路が見つからなかった。|
| D.D-7 | `hno : NoRawBelow D raw.name (n+1) raw`（DCEntryR.lean:14 の def、`resetNk_transport` :50、`runModuleTG_transport` DCEntryT.lean:119,156）。per-run、`raw` は存在量化 | `noRawBelow_of_closeInsts`/`…G` DCEntryS.lean:27/36 @base（承認済み）。`noRawBelow_of_coreRun` DCEntryU.lean:17 @kjob/g5dc-r23:74343ad8（未レビュー、clean build 未） | **U**（候補 R: `noRawBelow_of_coreRun`。leaf と (a3) が残る） | 読み: `noRawBelow_of_coreRun (d) (hS : Start L mctx cctx w) (hr : RunsTo (synthesizeCombinationalCore declName [] false) …) (hdef : MachineDefines … declName d.shape) (hcl : MachineClosesAtA L.O … d.shape) (hins : d.shape.insts ≠ []) (hf : d.shape.instFields = []) : ∀ k, NoRawBelow D raw.name k raw`。`hS` は EntryWitness の前件（A.P-02）、`hdef`/`hcl` は T1Hyp.defines/closes（A.P-06、既存行）、`hf` は `instFields = []`（一般の閉包の場合分け。別枝は `closeInstsG` 側）。**`hins`（leaf = insts が空）と最適化 body（a3）は DC_CONNECT_NORAW_FREEZE / D_M5t2 が未供給と明記**。base 392dc221 には DCEntryU が無い。|
| D.D-8 | `hlk : ∀ mn, mn ≠ rn → moduleByName D'.modules mn = moduleByName D.modules mn`（DCEntryR.lean:24、DCEntryT.lean:13,120,157） | `postEntry_lookup_ne` DCEntryN.lean:84、`synthesizeCombinational_postEntry` DCEntryD.lean:28、`o1_default` DCEntry.lean:43 @base 392dc221（承認済み seq4318/4497/4700） | **P**（default route）／parametric は D.D-2 の `Post` が未供給で対象外 | 読み: `postEntry_lookup_ne (h : PostEntry b raw D D') (hne : mn ≠ raw.name) : moduleByName D'.modules mn = moduleByName D.modules mn ∧ childMap … = childMap …`（証明済み）。`PostEntry` は `RunsTo (synthesizeCombinational declName) …` から `synthesizeCombinational_postEntry` が出す（default route）。DCEntryR.lean:56 は既に `have hlk` を中で作っている。台帳 `[PA]`（derived）と一致。parametric route の `Post` は D.D-2（A.P-05 に merged、この表の対象外）。|

## 2. 件数

17 行: **P 8**（C.SM-7, C.AC-7, C.AC-9, C.CV-5, C.DG-1, D.D-3, D.D-8, C.SM-1 の hs 半分）／**R 1**（C.CV-6）／**U 6**（C.SM-6, C.AC-4, C.AC-5, D.D-4, D.D-5, D.D-7）／**X 2**（C.CV-4, D.D-1）／**D 0**。
内訳の注意: C.SM-1 は「P（hs）＋U（被覆）」の分割で、被覆半分は C.AC-4 と同じ義務。C.DG-1 と D.D-3 は条件付き（行の数え方・GP の選択が reviewer／ユーザー判断）。確かさ 高: C.SM-7, C.AC-9, D.D-8。中: C.AC-7, C.CV-5, C.CV-6, C.DG-1。低: D.D-3, C.AC-5, D.D-7。

## 3. R/P の有望候補

### 候補 1: `hcb` の補題（C.CV-6 を消す）

* 消える ID: **C.CV-6**（`hcb`, R-in, R-dom の 3 つ全部）。
* 消える条件: (a) `hcb` の補題（下）、(b) R-in/R-dom が `readerTrace_final`（ShapeInputs'/TrInv）で供給済みであること。(b) は RT_ADMIT_DECISION の (A)（仮定を計上）が前提。(B)（条件付きのまま）や (C) では R-in/R-dom の供給が行に落ちないので、C.CV-6 は消えない。
* 残る条件: C.CV-4（`hfb`）、readerTrace_final の仮定（hv hbr hraw hnode hrr …、(A) で計上されるもの）、`hd`（carrier = `dataOfAt lvl`）。
* root theorem 型案:

```lean
theorem hcb_of_production {lvl : Lean.Expr → Nat} {dd : DefinitionVal} {senv : StructEnv} {sp : MachineShape} {d : MachineData}
    (h : machineShape? false [] (ConstantInfo.defnInfo dd) senv = some sp)
    (hd : Tools.ShippingGen5DataOf.dataOfAt lvl (ConstantInfo.defnInfo dd) senv sp = some d) :
    ∀ k (hk : k < d.shape.insts.length),
      (d.shape.binders[kDOf d + k]?).map (·.2) = some (d.shape.insts[k]'hk).2.2
```

  証明の筋: `machineShape?_callBinder h`（bs, e と peel 等式、位置 `bs.length + k`）、`dataOfFrom_nIn`（同じ peel p と `d.nIn = p.1.length + sp.insts.length`、peel の一意性で `p = (bs, e)`）、`kDOf d = bs.length`（`kDOf_eq_nDeclOfCi_of_dataOfFrom` ReaderTraceKDOf.lean:15 と同じ手筋）、`dataOfFrom_dims` の `d.shape = sp`、`List.getElem?_map`。
* 費用: 約 25-40 行（新規ファイル 1 本＋ Check）。確かさ 中（読みのみ。`allow` 引数のデフォルト、`Option.map` と `getElem?_map` の整形が通るかは未確認）。
* 新しい freeze／TRUSTED: freeze 要（前提の除去なので reviewer）。TRUSTED／law は不要。
* 新しく増える行: 0。ただし統合 tree（ShippingMachineShapeTail は base にあるが DataOfDims は rt 系の tree）が要る。
* 注意: 台帳 C.CV-6 の「`hcb` は B3」は別行の取り違えに見える（上の表）。B3（b23 の letSort 4 等式）は C.SM-6 の残りで、CV-6 には含まれない。

### 候補 2: carrier を `dataOfAt lvl` に固定する一括単位（C.AC-9, C.CV-5, C.SM-1 の hs 半分）

* 消える ID: **C.AC-9**（`hDS`、`RunDataLink` は cover ルートで不要）、**C.CV-5**（`hsp hss hls hn`）、C.SM-1 は hs 半分のみ（被覆半分が C.AC-4 に残るので、行を消すか C.AC-4 に merged とみなすかは reviewer 判断）。同じ固定で C.AC-1（merged 済み）も消える。
* 消える条件: ルート定理の dataOf を `fun E se s => dataOfAt lvl E se s`、`initsOf := Tools.ShippingGen5DataOfPure.initsOf` に固定すること。`lvl` は自由変数のままで良い（健全性は `lvl` に依らない。被覆の仮定は C.AC-4 に残る）。
* 残る条件: C.CV-4（`hbr`）、C.AC-4（被覆。`hd` は `GenData.hdata` から来るので新しい仮説にはならない）。
* root theorem 型案:

```lean
theorem dataOfSound_dataOfAt (lvl : Lean.Expr → Nat) :
    DataOfSound (fun E se s => Tools.ShippingGen5DataOf.dataOfAt lvl E se s) Tools.ShippingGen5DataOfPure.initsOf :=
  fun _ _ _ _ h => Tools.ShippingGen5DataOf.dataOfAt_sound lvl h

theorem dataOfShape_mkKit_dataOfAt (lvl) (env₀) … (hev hloc hdecl hd …) :
    DataOfShape (mkKit (fun E se s => dataOfAt lvl E se s) (GenData … ) … (genDataC … env₀) ordCallees₀ …)
  -- dataOfShape_of_sound ∘ mkKit_dataSound (hf := fun E se s d h => ⟨(dataOfAt_sound lvl h).1, (dataOfAt_sound lvl h).2.1, (dataOfAt_sound lvl h).2.2.1⟩)
```

  C.CV-5 側は、ルートで `shapeAgree_witness hbr h hd`（GDCover1.lean:58）を呼んで `ShapeAgree d st` を得る（`hsp…` が仮説に残らない）。
* 費用: 40-80 行（統合 tree 作りは別）。確かさ 中-高（`initsOf` の型一致は読みで確認。`tys` の同一性は DataOfPure.lean:354 と SemGenData.lean:19 の開き方が同じことを見たのみ）。
* 新しい freeze／TRUSTED: freeze 要（前提の除去）。carrier 固定は GDCOVER01_RESULT の (c)、D3 に近いが `dataOfAt`（承認済み）をそのまま使うので意味の変更はない。ただし `dataOf` を `dataOfAt lvl` に限ることは、GenData-kit の汎用性を狭めるので reviewer に見せる。
* 新しく増える行: 0。

### 候補 3: ReadsSupplyAt を EN-1 + RK-1 に置換（C.AC-7）

* 消える ID: **C.AC-7**。
* 消える条件: ルート定理を強化法則 `L'` 上で述べ、`readsSupply_of_quiet`（AccReads.lean:99）を適用する。
* 残る条件: C.EN-1（`QuietStrengthA L L' env₀`）、C.RK-1（`ReadKeeps cref` → `GetEnvFrame`）。どちらも既存の FG 行。
* 型案: `readsSupply_of_quiet (hq : QuietStrengthA L L' env₀) (hg : ∀ mctx cctx, getEnvFrame_of_readKeeps hk) Reach : ReadsSupplyAt env₀ L' Reach`（証明済みの定理をそのまま適用）。`accServed0_of_cover_gates` の `L` を `L'` として使う。
* 費用: 20-40 行（ラッパのみ）。確かさ 中（`L` と `L'` の混在: 他の前提 `hC : ClosesOfShape env₀ L' Reach` なども `L'` 版にする必要があり、`closesA_up` / `t1HypND_up`（EnvQ、別系列の branch）との整合は読んでいない）。
* freeze: 要（前提の除去）。新 TRUSTED／law なし。増える行: 0。

### 候補 4: C.SM-7 の `hord`（`h_D_T1` を `genExtAtCall_of_genSem` で閉じる単位）

* 消える ID: **C.SM-7**（`[PA]`）。
* 消える条件: `h_D_T1` の証明で `genExtAtCall_of_genSem … (hord := ‹内側の前件›)` を使う（`originOf p.d k` は定義で `p.d.shape.instOrigins.getD k .ord` に一致）。
* 残る条件: D.T-1 の他の前提（`hp : p.toSem = genSemI (semOf P) X g`、`hq`）。
* 費用: 5-15 行。確かさ 高。freeze は「前提の除去」として要。増える行: 0。独立の単位にするより、D.T-1 側の組み立て単位に含めるのが自然。

### 候補 5（条件付き・要ユーザー判断）: GP を `genP` に固定（D.D-3, C.DG-1）

* 消える ID: **D.D-3**、**C.DG-1**（(i)(ii) は C.AC-4／C.SM-6 の言い換えとみなす台帳 §11.3 の見方が前提）。
* 消える条件: ルートで `GP := fun env => genP (K env) (factsOf_genS_assembled'' hs (genDataC dataOf env))`。結論 O2 は `genP_pkg`（hcl hacc hcov hOk）から。
* 残る条件: C.AC-4（hcov）、C.AC-8（hacc）、A.P-20（hOk=DataOk）、C.SM-1（hs）。いずれも既存行。
* 型案: `GP` の定義と `genP_pkg` を `FG_CONNECT` の前件に差し込む形（FG.lean:54 の型は変えない。`GP` を具体化した特殊化が結論）。
* 費用: 100-200 行（env 全体で定義する、`FG_CONNECT` との結線、統合 tree）。確かさ 中-低。
* freeze 要。「GP を genP にする」は FG の結論を DGEN 経路の packages に特殊化する選択で、台帳／ユーザー判断が要る。新しく増える行: 0（見込み）。減る行: D.D-3 と C.DG-1 の計 −2（C.DG-1 を数えるかは判断）。

## 4. 経路が見つからなかったもの（U）の一言ずつ

* C.SM-6: 6/7 連言は R 候補だが、B3（b23 の `letSort` 4 等式）が残る。候補: T1L-66 `MemSrcKinds`／T1L-47 `ReadTyped`（src-argw）に `letSort` を結ぶ補題。この調査では補題名が見つからなかった。
* C.AC-4: (D) が `dataOfFront` の条件 3（dom 一致、D1/D3 の判断待ち）、4（C-QWIT）、8（S-OK）で止まる。(S) は callee ごとの run が要る。
* C.AC-5: `runReads → GateRunsAt` の継ぎ補題が無く、`c ∈ Reach` ごとの run が要る。候補: `RunReadsAt.gates`＋AC-7、または A.P-06（`MachineDefines`）。
* D.D-4: `ConstValue` の定義が無い。
* D.D-5: `hstep`（rows 0-4）が未供給。`hclosed` と `hAcc` は取れる。
* D.D-7: `noRawBelow_of_coreRun`（74343ad8）が候補。leaf／(a3) が未供給で、未レビュー。

## 5. 追加の観察（この表の対象外だが関連）

* `GenData` carrier では C.AC-2（`hev`）と C.AC-3（`hloc` `hdecl` `hd`）が `genData_gdEvidence`, `genData_genSem_local/decl/d`（AccGenDataKit.lean:11-30）で P。C.SM-3/SM-4/SM-5 は `hinv_genS`（AccHinv.lean:18）以降の `factsOf_genS_assembled''` で `hs` だけに帰着する。別担当の行だが、候補 2 と 5 の前提として効く。
* readerTrace_final の `hbranch` は `entryConst`（Elab.lean:5277）の定義から出る形で、`hEd` は `peel_of_machineShape`（GDCover0.lean:71）から出る。これらを継ぐ「run → readerTrace_final」の薄い橋（`RunReadsAt` → `h` `hbranch` `hci` `hEd`）は Lean にまだ無い。AC-4 の (S)、AC-5、AC-7 が同じ橋を使うので、1 本立てると効く。
* 台帳の記述の食い違い: (1) C.CV-6 の `hcb` ≠ B3、(2) C.CV-5 の「`st` は run-local」は結論の ∃ で、run-local ではない（§0.1）、(3) C.AC-4 の「kit K / Reach carrier not fixed」は `mkKit … genDataC …` と `ReachEdge K Top` で固定できる。いずれも台帳の文は変えていない。

---

## 担当 5

### out_5: D.T-1, D.T-2, D.T-4, D.E-4, D.E-12, D.E-13 と、§12.1/§12.8 で後から加えた 7 行（束縛変数の出口）

調べた base: 392dc221 (par/hord-run)。他 branch は `git show` / `git grep` で読んだだけ。Lean は 1 本も走らせていない（build なし）ので、下の根拠はすべて「読み」。「見つからなかった」は「この調査では供給元・経路が見つからなかった」の意味で、不可能とは言っていない。mutant は扱っていない。

SHA の略記: rtF = par/rt-final@378f8e31、candA = kjob/candA-int@6a167f19、ua7d = par/aud-ua7d@1e98d041、fgls = par/fg-ledger-sync。

## 分類表

| ID | 束縛変数(名:型の要点) | FG定理 file:line @branch:SHA | 分類 | 根拠・読み/確認 |
|---|---|---|---|---|
| D.T-1 | `h_D_T1` = `hDG_SEM : GenExtAtCall p q k hk`。`∀ i bools bits k' o f, q.outs[k']? = some o → CallField p q k o → (q.src …)[k']? = some f → SigAt (p.extBS …)(p.extS …)(p.kD+k) κ f`。ガードは `(p.d.shape.instOrigins.getD k .ord).child? = none`（ordinary のみ）と `GP env (insts[k]).1 = some q` | `FGLedgerPremisesStmt` の第 2 内側仮説 `Tools/ShippingGenFGLedgerPremises.lean:55-58`（base）。定義 `Tools/ShippingGen5T2Tie.lean:238`。消費側 `callTie_of_served_oneOut_t1ND` / `callTie_of_served_kidW_closing_t1ND` の `hDG_SEM`（`Tools/ShippingGen5T1ND.lean:99,116`、base） | **D**（DG-SEM / 生成器の Pkg の性質）。run からは出ない。条件付きの置換候補が 1 本（下記候補 3） | 読み: ClosingRun の `shared` 末尾 `MachineTraceLBX … p.src p.extS p.extBS p.lsrc`（`Tools/ShippingGen5ClosingRun.lean:62-65`、`Tools/ShippingMachineTraceX.lean:377-`）は `ext`/`extB` を全称の関数として受け、`SourceInputs … (extB …)(ext …)` を前件にして `src` を結論にする。`ext` の `kD+k` 番目が callee の `src` 出力と一致することは、run のどこにも書かれていない。`RealChildA`（`Tools/ShippingChildCacheA.lean:105`）は子の合成 run の履歴だけで、親の Pkg の `extS` に触れない。T1 の `T1Hyp.dec`（`Tools/ShippingGen2Defs.lean:117` の `posEnc … extBS extS`）が同じ中身。具体的な供給の定理は `Tools.ShippingGen5Sem.genExtAtCall_of_genSem`（candA の `Tools/ShippingGen5SemExtPkg.lean:17`、approved 7c06a80f）で、前提 `hp : p.toSem = genSemI (semOf P) X g`、`hq`、`hord`。`hq` と `hord` は h_D_T1 のガードそのもの。`hp` は `GP := genP K hF` のとき `genP_generated`（`Tools/ShippingGen5AccGenP.lean:96`、candA）から出るが、`hF : GenSFacts K`（DG_ACC_FREEZE_REV4 §2 R7）は DG-SEM の P6'/P11 待ちで未供給（DG_SEM_FREEZE_P6C §2 行 5d）。T1 台帳 §8 の「FG が払う」は、この Pkg 生成側の義務を指す |
| D.T-2 | 束縛変数なし（FGLP の Lean 名は `-`）。`hDG_SEM_range : CallOutRange p q k hk`（`T2Tie.lean:250`）は `callTie_of_dgen`/`callTie_of_served`（`T2Tie.lean:262,283`）の引数としてだけ残る | `callOutRange_of_widths`（`Tools/ShippingGen5T2Range.lean:162`、base）。`Pkg.src_range`（同 :122）。ND 側の root は `CallOutRange` を取らない: `callTie_of_served_oneOut_t1ND`（`T1ND.lean:~86`）、`…kidW_closing_t1ND`（同 :~108）、`callTie_of_served_widths`（`T2Conn.lean:~39`） | **P**（派生。既に PA）。ただし減るのは表示上の非リーフ 1 行で、リーフは動かない | 確認（文面を開いた）: `FGLedgerPremisesStmt` の内側仮説 3 つは `h_A_P06`（MachineDefines）、`h_D_T1`、`h_D_T4` だけ（`Tests/Gen5/FGLedgerPremisesCheck.lean:49-62`）。`CallOutRange` は FG の root の束縛変数に無い。読み: `callOutRange_of_widths` の前提は (a) `houtTy`（`houtTy_of_closingND`、`T1ND.lean:~70`、T1HypND.defines と RealChildA から。D.T-9）、(b) `CallOutWidthAt p q k` = D.T-3 `OneOutWidth`（`callOutWidthAt_of_oneOut`）または D.T-4 `hkidW`（`callOutWidthAt_of_kidW`）。独立した束縛変数が無く他の行で数えているので、A.P-22（FG 台帳 §12.7、`LEDGER_NONLEAF_CHECK`）と同じ型。残る内容は D.T-3 / D.T-4 に移っている |
| D.T-4 | `h_D_T4` = `hkidW : ∀ k hk y, RealChildA L.O (p.insts[k]).1 y → ∀ pt ∈ y.1.outputs, pt.name = p.instFields.getD k "" → (p.binders[p.kD+k]?).map (kindTy ·.2 |>.bitWidth) = some pt.ty.bitWidth`。ガードは `TgtRun (GP env) declName c` と `GP env c = some p` | `Tools/ShippingGenFGLedgerPremises.lean:59-64`（base）。消費側 `callTie_of_served_kidW_closing_t1ND`（`T1ND.lean:~108`）、`callOutRange_of_closing_kidW`（`T2Conn.lean:105`）、`callOutWidthAt_of_kidW`（`T2Range.lean:~213`） | **D**（宣言ペアのデータ性質 `callWidthsOk`。M3/gen3 データ供給側）。run（RealChildA, ClosingRun）からは出ない | 読み（run から出せるかの確認）: `RealChildA`（`Tools/ShippingChildCacheA.lean:105`）は子 `c` の `synthesizeCombinational c` の run 1 本で、子側の `y.1.outputs` だけ。親の `binders[kD+k]` は親の `RunReadsAt.shapeEq`（`machineShape?` = `p.d.shape`）にあるが、2 つを結ぶ文が無い。結ぶのは `callWidthsOk d nDecl kidOuts`（`Tools/ShippingCallWidths.lean:51`）→ `hkidW_of_data`（同 :62）/ `hkidW_of_dataA`（`Tools/ShippingParentRunFactsA.lean:612`）で、行 `callWidthsOk = true` と `ChildOutTys (kidOuts k) y.1`（`Tools/ShippingChildIfaceTy.lean:47`）を要する。(1) `ChildOutTys` を `RealChildA` から出す定理は leaf だけ見つかった（`leaf_real_outTysA`、`Tools/ShippingCallWidthsChildRealA.lean:~236`）。非 leaf の子は見つからなかった。(2) `callWidthsOk` を出す `callWidthsStrict_realA`（同 :~58）は callee ごとの `ResDeclAt` / `P5At`（`Tools/ShippingCallWidthsChildReal.lean:137,147`）と `PB`（親 binder の kindTy = `machHWType res`）を仮定とし、これらは run の事実ではなく「宣言の結果型 `machResultKind?` の読み」の一致。(3) コンパイラ側に幅の突合ゲートは無い: `git grep instOutWidthsOk|portsMatchB|designCheck -- Sparkle` は 0 件（確認）。`machineShape?_noMemRow`（hord の手本の出所）に当たる最終ゲートが幅にはない。メモリ子だけは `hkidW_of_memOrigin`（`Tools/ShippingGen2MemFacts.lean:20`）で出るが、h_D_T4 のガードは非 mem に限っていない |
| D.E-4 | 束 B3/B4/B5。`machineClosesAtA_of_memKids'`（`Tools/ShippingCallsMemPinned.lean:330`、base）の `hparentD`（B3: `ofDecl declName ∉ namesK k`）、`hdisjD`（B4: 異なる callee/memKey の `nameK k ∉ namesK k'` ∧ `∀ x ∈ namesK k, x ∉ namesK k'`）、`hfresh`（B5: `∀ gi k, ∀ o ∈ layout.outs, o.name ≠ s!"inst{gi}_{nameK k}"`）。Audit 形は `AuditE4_B3B4` / `AuditE4_B5`（`scripts/gen5/AUDIT_CARRIER_FREEZE.md:73-88`） | FG の root の束縛変数としては見つからなかった（`FGLedgerPremisesStmt` に E-4 は無い）。B3 の供給: `auditE3B3_of_t1hyp_run`（`Tools/ShippingGen5AuditE3B3Run.lean:273`、base。結論 `AuditE3 ∧ AuditB3`）。`AuditB3` は `Tools/ShippingGen5AuditE3B3.lean:741` | **行としては残る（0）**。部分ごと: B3 = **P**、B4 = **X**（ユーザー判断で文を残す）、B5 = **U** | 下の「D.E-4 の部分」を参照 |
| D.E-12 | `hno : ∀ x ∈ D.modules, x.name ≠ raw.name`、`htop : D.topModule = raw.name`（`hcore : RunsTo (synthesizeCombinationalCore declName [] false) … (raw, D) w2` の上） | `writer_prints_endpoint_artifact` `Tools/ShippingDesignWriterRun.lean:119-128`（base）。他の消費側 `PostFactsStmt` 結論 (i)（`Tools/ShippingGen2PostFacts.lean:39-55`）、`ihAt_stepPF`（`Tools/ShippingGen2T1.lean:164-196`）。Audit 形 `AuditE12G`（`Tools/ShippingGen5AuditE12G.lean:24`、ua7d、approved 7feca8b0。base に無い） | **U**（部分ごとに下記。run の局所事実として出る部分はあるが、定理として通ったものは machine 側の一部のみ） | 下の「D.E-12 の部分」を参照 |
| D.E-13 | 束縛変数なし。`emitModule`（G7-c 印字） | FG の定理に現れない | **X**（設計上 TRUSTED、保証の外） | 読み: FG 台帳本文と boundary-audit §3 が「TRUSTED by design（printer）。parse-back は validation のみ」。FG 台帳では「除外」3 行の 1 つ。出口を探す対象でない。型は読んでいない |
| SigTyClosed（§12.1） | `hC : SigTyClosed (structEnv env)`。`∀ c kinds ty, senv.instS c = some (kinds, ty) → BvarLt 0 ty = true` | 定義 `Tools/Assume/EnvSigTy.lean:32` @rtF（4d6b9719 で登録）。消費側 `readF_traceGood_of_premises`（`Tools/ShippingGen5ReaderTraceDispatch.lean:105`）、`readerTrace_final`（`Tools/ShippingGen5ReaderTraceFinal.lean:10`）@rtF。**base に無い**（`git log --all -S SigTyClosed` で 4d6b9719 / 76c134b6、par/rt-final ほか） | **X**（環境の事実。`Lean.Environment` は未モデル化） | 読み: `instSignatureS_type`（`Tools/ShippingLetsSigTy.lean:~73`、証明済み）で `ty` は環境の定数の宣言型 `ci.type`。必要なのは「宣言型が閉じている」というカーネルの事実で、T1L-53 `EnvTypesFVarFree`（`NoFv ci.type`、`LetsSigTy:63`）は fvar の不在であり loose bvar の不在を含まない（EnvSigTy.lean ヘッダも同じ説明）。run の事実ではない |
| InstSFieldsDet（§12.1） | `hD : InstSFieldsDet (structEnv env)`。同じ `instS` 署名の任意 args 2 組について `machOuts?` の fields 数が等しい | 定義 `Tools/Assume/EnvInstS.lean:31` @rtF（206c39a2）。消費側 `readF_traceGood_of_premises`（Dispatch:105）、`readerTrace_final` @rtF。base に無い | **X** | 読み: `instSStep` の dedup arm だけが使う。結果型の head 定数が args に依らない、という型付けの事実で、環境の外の `partial def`（`machOuts?`）の読みに依存。run からは出ない。Option B `SigResHeadConst` は不採用（EnvInstS.lean ヘッダ） |
| N1-a DeclValuePh（§12.8） | `hv : DeclValuePh env`。`∀ n d, env.find? n = some (.defnInfo d) → NoPh d.value = true ∧ BvarLt 0 d.value = true` | 定義 `Tools/Assume/EnvDeclValue.lean:22` @rtF。消費側 `readerTrace_final`（Final.lean:10）、`shapeInputs_of_direct'` / `shapeInputs_of_inline'` @rtF。base に無い | **X**（環境の事実） | 読み: RT_U2_FREEZE §1 と DG_READERTRACE_FREEZE_REV16 §2.3 が重複照合済み（reviewer 結論: 既存の行に含まれない新規の文）。T1L-53 は型だけで値を含まない。N1-b（`EnvTypesFVarFree` を値まで強化）は REV15 で「既存行の強化＝新規扱い」とされ採られていない |
| N2-b PackTupleInputsBridge（§12.8） | `hbr : PackTupleInputsBridge`。`∀ e, NoPh e → BvarLt 0 e → packTupleInputs e = packTupleInputsF (lamDepth e) e` | 定義 `Tools/Assume/PackTupleBridge.lean:39` @rtF。消費側 `readerTrace_final` @rtF。base に無い | **X**（コンパイラ内部の `partial def` の等式。論理の中に本体が無い） | 読み: REV16 §3.4。C.CV-4 `FuelBridge`（`machineShape?` と `machineShapeF` の一致）は `packTupleInputs` の twin を含まない別の文。T1L-30 `hkD` も範囲保存・twin 一致を含まない。除く道 N2-c（コンパイラの `packTupleInputs` を全域化）はコンパイラ編集でユーザー判断が要る |
| N3-b RawNodePh（§12.8） | `hraw : RawNodePh (structEnv env)`。`rawNode senv.prodMatch (.app f a) = some e'` が `NoPh ∧ BvarLt L` を保つ | 定義 `Tools/Assume/NormNodePh.lean:21` @rtF。消費側 `readerTrace_final` @rtF。base に無い | **X**（`rawNode` 内の `Expr.beta`（`partial def betaRev`）等の外部関数の範囲保存） | 読み: REV16 §4.3。T1L-55/56（`LiftAgrees0` / `LowerAgreesEq`）は lift/lower の spec 一致で範囲の文でない。T1L-57 `BetaRange` は `LetOk` の文で `BvarLt` を含まない。`RawNodeRange`（`Tools/Prototype/NormRangeLetOk.lean:23`）は `LetOk` 版で別の性質（base にあるが NoPh/BvarLt 版の証明は見つからなかった）。分解は N3-c 待ち |
| N3-b NormNodePh（§12.8） | `hnode : NormNodePh (structEnv env)`。`NoPh (machNormNode senv (.app f a)) ∧ BvarLt L …` | 定義 `Tools/Assume/NormNodePh.lean:26` @rtF。消費側 `readerTrace_final` @rtF。base に無い | **U**（候補 N3-c あり。条件は branch 統合待ち） | 読み: REV15 §3.3 の N3-c = `machLiftScalarN` / `machBoolMap` を `par/ptot-m4` 965fe51b（全域化と一致定理 `liftScalarCorr` / `boolMapCorr`、T1L-58/59 を T1 台帳から除いた）の上で Ph 保存を証明して `NormNodePh` を定理にする。ptot-m4 は base に入っていない（`git merge-base --is-ancestor 965fe51b HEAD` が偽、確認）。モデル側の Ph 版の補題が新規で、約 40 arm の構造補題が要る（規模は REV15 に数字なし） |
| RecRulePhU（§12.8） | `hrr : RecRulePhU env`。`env.find? (.str p "rec") = some (.recInfo rv) → rv.rules.find? (·.ctor == c) = some r → NoPh r.rhs ∧ BvarLt 0 r.rhs` | 定義 `Tools/PassPh/Defs.lean:17` @rtF。消費側 `shapeInputs_of_inline'`（`readerTrace_final` から呼ぶ）@rtF。base に無い | **X**（環境の事実） | 読み: RT_RECRULE_FREEZE §1.2・§5。N1-a の recursor 規則版で、別の行（FG 台帳 §12.8 の裁定）。`Defs.lean` のヘッダに「hypothesis definition only」とあるが、台帳は §12.8 で +1 として計上済み |

件数（13 行）: R = 0、P = 1（D.T-2）、D = 2（D.T-1, D.T-4）、U = 2（D.E-12, NormNodePh）、X = 7（D.E-13, SigTyClosed, InstSFieldsDet, DeclValuePh, PackTupleInputsBridge, RawNodePh, RecRulePhU）、束行 1（D.E-4: B3 = P、B4 = X、B5 = U で、行は残る）。

## D.E-4 の部分（B3 / B4 / B5）

| 部分 | 状況 | 分類 | 根拠 |
|---|---|---|---|
| B3 `hparentD` の名前の部分 `ofDecl declName ∉ namesK k` | 既に供給済み。`auditE3B3_of_t1hyp_run`（`Tools/ShippingGen5AuditE3B3Run.lean:273`、base）が `AuditE3 ∧ AuditB3` を出す。仮説は `T1Hyp`、T1L-12 `hMemRow`、新 T1 行 `hLeafAlias`、`AdmCtx`、E-5 carrier（`hin` `hsp` `hg`）。`hrow` は無い（FG 台帳 §12.6） | P | 読み: `AuditB3`（`AuditE3B3.lean:741`）の docstring が「`namesK k` を kid の top と design の名前に取った B3 の部分。`ChildIfaceP` の他の field と B4 は含まない」と明記。つまり `AuditE4_B3B4` の `∃ nk outsK namesK, ChildIfaceP …` の存在までは出していない。定理 `machineClosesAtA_of_memKids'` の `hparentD` を `AuditB3` から実際に渡す接続も、この調査では見つからなかった（Audit 形の文のまま） |
| B4 `hdisjD` | 文を変えずに残す（ユーザー判断 (3)、2026-11-03、`scripts/gen5/AUD_B4_DECISION.md`、FG 台帳 §12.5）。共有する子孫がある設計では B4 が偽で、FG はその設計について空虚（実測: 階層のある 29 本中 1 本、IP は 0 本） | X（文の変更はユーザー判断済みで「残す」） | 読み: B4 が要るのは「同じ名前の module は同じもの」のためだけ（A-shared-descendant §1）。代替は案 (2) `CacheAgrees` 型への置換（保証が広がる、供給は未確認）。run からは出ない（2 つの異なる子の design の module 名の互いの非交差は、cache の終端 world の性質） |
| B5 `hfresh` | 未判断。推奨は (d)「前提として残す」（`scripts/gen5/AUDIT_B5_DECISION.md`、par/aud-b5 b7dd1abf）。FG の範囲を狭めないという読みまで付いている | U | 読み: `instStmtG` が `names.contains instName` なら `none`（`Sparkle/IR/MachineInstG.lean:46-48`、`Sparkle/IR/Machine.lean:283-285`）を返すので、`closeInstsG = some` の run からは「実際の group 添字 gi と実際の子名」についての非衝突が出る。ただし (1) B5 の文は `∀ gi k` で、run が与えるのは実在の (gi, k) だけ。(2) B5 は `machineClosesAtA_of_memKids'` が `MachineClosesAtA`（全 `AdmCtx` の上の machine 成功）を作るための前提で、run の `MachineTaken` から取ると T1Hyp.closes（G-CLOSES）の導出が循環する。(3) B5 が偽の設計はコンパイルが legacy route に落ちて通る（AUDIT_B5_DECISION §2.6 の 1 件の観測）ので、FG の範囲内の legacy の保証（M4 の契約）の話になる。候補: 実在の (gi,k) に弱めた B5' を `CloseCalls` から出し、T1 側の closes を run 版にする。これは `closes` の文の変更なので X 扱いで、ここでは提案しない |

行 D.E-4 は B4 と B5 が残るので、B3 が P でも行は消えない（FG 台帳 §12.6 の裁定と同じ）。

## D.E-12 の部分（hno / htop × machine / 非 machine）

| 部分 | 供給状況 | 根拠 |
|---|---|---|
| htop、machine route | run 局所の事実として存在しうる。定理は「Lean に入っているもの」と「scratch だけ」に分かれる: `closeMachine … .name = ofDecl declName`（`Tools/ShippingCacheCoherentCert.lean:~425,575`、`ShippingCacheCoherentData.lean:41`、base）。`Machine.designWith` / `closeInsts` の design の topModule の側は読んでいない | 読み: FB_HNO_STUDY §1.3 の表（par/fb-cycle5）。`AuditE12G`（machine route の guard 付き、ua7d）の中身の定理 `e12_closingRun`（leaf 枝は無条件）は UA7b の scratch のみで tree に無い（`git grep e12_closingRun` は branch 全体で 0 件、確認） |
| hno、machine route・leaf（insts = []） | gate leaf の `hno_of_full_empty` が UA7b に言及されるが、tree には見つからなかった（`git grep hno_of_full_empty HEAD` 0 件、確認） | 読み: AUD_UA7B_STUDY §2 |
| hno、machine route・calls 枝 | 子側 `hsep'`: 2 半分。(a) 子自身の名前 `ofDecl callee ≠ ofDecl declName`: `hself_all_reached`（`Tools/ShippingGen5NameKids3.lean:99`、base）が `InClass`（D.E-8 の `hnd`/`hr`）+ `GraphAgrees` + `ReachSpans` から出す。(b) 子の design の module 名が `ofDecl declName` でないこと: この調査では供給元・経路が見つからなかった。別の `NoRawBelow`（D.D-7、`Tools/ShippingGen5DCEntryS.lean:27 noRawBelow_of_closeInsts`）は instance 文の `mn ≠ rn` で `D.modules` の name の文ではなく、`hno` と別 | 読み: UA7b §1、FB_RESUME_STUDY §3.2。`ofDecl_injective`（`Tools/ShippingModuleName.lean:766` 付近、既存定理）は新前提を要さない（FB_HNO_STUDY §2.1、scratch で axioms 3 つ） |
| htop、非 machine route | 小補題（init/finalize/addClockReset/finishSynth が name・topModule を保つ）は scratch で通っただけ（tree に無い）。certified / mixed の transition 形には `transition_closed`（`Tools/ShippingTransitionClosed.lean:35-56`、base）がある。gate cone には `desFinal_of_run`（`Tools/ShippingGateDesignWalk.lean`）。legacy と任意 body の mixed: circuit state を追う不変量が見つからなかった（`TripleC` / `Keeps` は world だけ追う）。outermost の memo miss の `outer_miss`（`Tools/ShippingLegacySemMemoWalk.lean:495`）は `RefLawsM` 前提（保留中） | 読み: FB_HNO_STUDY §1.3（par/fb-cycle5）。推定規模は「約 1874 行」（FG 台帳側 cmp.md §3 の引用。FB_HNO_STUDY の数字ではない点に注意） |
| hno、非 machine route | acyclic な呼び出しグラフの下で成り立つように読めるが、run から acyclicity を出す補題は見つからなかった。`tryInlineUnfold` の catch / retry が入れ子の throw を飲めるので depth 上限 1024 だけでは閉じない。`synthesizeHierarchical` の成功は `hno` と同値の分岐（`hno_iff_not_any`、scratch）で、成功から `hno` は出ない。直接自己再帰の 1 例は depth 上限で throw（観測 1 件） | 読み: FB_HNO_STUDY §2。`AuditE12G`（案 A）はこの部分を E-12 の行から外して M4 の route 別義務に移す（行が増えるかは M4 の freeze 次第）。ユーザー quiet C（2026-11-04）で 1c は実装しない |

D.E-12 全体: hno / htop が束なので、machine 側がどれだけ出ても行は消えない。ua7d の `AuditE12G`（文の変更）を受理しても行は残る（`hsep'`(b) と非 machine 分が残る）。

## R / P の有望候補

R は見つからなかった。理由: 今回の 13 行は、どれも「run の束縛変数が run 自身の `shapeEq` やコンパイラの最終ゲートから出る」型（hord の手本 (a)）に当たらない。D.T-4 は宣言ペアの幅の突合（ゲート無し）、D.T-1 は Pkg の `ext` の選び方（run は ext を縛らない）、残りは環境・コンパイラ内部の事実。

### 候補 1（P）: D.T-2 を非リーフの表示から除く（A.P-22 の前例）

| 項目 | 内容 |
|---|---|
| 消える ID | D.T-2（PA、非リーフ） |
| 消える条件 | FG の root（`FGLedgerPremisesStmt` の内側仮説、ND 側の `callTie_of_served_*_t1ND`）の束縛変数に `CallOutRange` / `hDG_SEM_range` が無いこと（上の確認）。FG 台帳 §12.7 の A.P-22 と同じ理由「FG 側に独立した binder が無い、他の行で数えている」 |
| 残る条件 | D.T-3（`OneOutWidth`）、D.T-4（`hkidW`）、D.T-9（`houtTy`、`houtTy_of_closingND`）。旧 root `callTie_of_dgen` / `callTie_of_served`（`T2Tie.lean:262,283`）は `hDG_SEM_range` を取り続けるが、FG の root から使われない |
| root theorem の型案 | 新しい定理は不要。参照する既存定理: `callOutRange_of_widths (p q k hk) (houtTy : ∀ o ∈ q.d.shape.layout.outs, o.ty.bitWidth = o.width) (hW : CallOutWidthAt p q k) : CallOutRange p q k hk`（`T2Range.lean:162`） |
| 費用 | 文書のみ（`LEDGER_NONLEAF_CHECK` と同形の照合）。Lean 追加なし |
| 確かさ | 中。T2Tie の旧 root が FG の依存に入っていないことの照合（FG_CONNECT の閉包）はこの調査では実施していない |
| 新しい freeze / TRUSTED | TRUSTED 不要。台帳の表示変更なので reviewer 承認 |
| 増える行 | なし。合計 FG −1（非リーフ）。リーフは動かない |

### 候補 2（要ユーザー判断・X 寄り）: D.T-1 を `genExtAtCall_of_genSem` で置換

| 項目 | 内容 |
|---|---|
| 消える ID | D.T-1（TY-I） |
| 消える条件 | `FG_CONNECT` の carrier `GP` を `genP K hF` に固定し、`h_D_T1` の `GP env … = some q` のガードから `hq`、ガード `child? = none` から `hord`、`genP_generated`（candA `Tools/ShippingGen5AccGenP.lean:96`）から `hp` を作る |
| 残る条件 | `hF : GenSFacts K`（DG_ACC_FREEZE_REV4 R7。DG-SEM の P6' `GenFacts.causal`、P10/P11 が未実装）、`ReachCover`（R2、DG-COVER / DG-DATAOF）、`GenIn` の構成（`GenData.toIn`、見つからなかった） |
| root theorem の型案 | `genExtAtCall_of_genSem (P) (X) (g : GenIn) (p q) (k) (hk) (hp : p.toSem = genSemI (semOf P) X g) (hq : P (p.d.shape.insts[k]'hk).1 = some q) (hord : (originOf p.d k).child? = none) : GenExtAtCall p q k hk`（candA `Tools/ShippingGen5SemExtPkg.lean:17`） |
| 費用 | 定理自体は built（agent build、approved 7c06a80f）。FG_CONNECT の carrier を `GP := genP K hF` に特化する root の組み立ては未設計。供給元の未実装部（因果性）が大きい。行数の見積りは根拠なし |
| 確かさ | 低。`hF` が既存の台帳行（C.SM-*、C.AC-* 系）に当たるか新しい行かをこの調査では照合していない |
| 新しい freeze / TRUSTED | freeze 要（carrier の特化は FG_CONNECT の型の変更）。TRUSTED 不要のはず。GP の抽象 carrier を捨てる扱いは FG の statement の変更で、要ユーザー判断 |
| 増える行 | 不明（`hF` が新しい行になる場合 +1） |

### 候補 3（U・低い見込み）: NormNodePh を N3-c で定理にする

| 項目 | 内容 |
|---|---|
| 消える ID | N3-b NormNodePh（`RawNodePh` は残る） |
| 消える条件 | `par/ptot-m4`（965fe51b）を統合し、`machLiftScalarN` / `machBoolMap` の全域版と一致定理から `NoPh ∧ BvarLt L` 保存をモデル上で証明し、`machNormNode` の約 40 arm の構造補題と合わせる |
| 残る条件 | `RawNodePh`、`Inst1Agrees`（T1L-51）、ptot-m4 が仮定する事項 |
| root theorem の型案 | `normNodePh_of_models (senv : StructEnv) (hi1 : Inst1Agrees) … : NormNodePh senv`（未命名。REV15 §3.3 の記述のみ） |
| 費用 | 大（Ph 版のモデル補題が新規。REV15 は行数を書いていない） |
| 確かさ | 低 |
| 新しい freeze / TRUSTED | freeze 要。ptot-m4 の統合が先（ユーザーの merge） |
| 増える行 | 0〜+1（REV15 の見込み。この調査で数えていない） |

### 候補としないもの

* D.T-4、D.E-4 の B4/B5、D.E-12 の非 machine 分: 上の根拠のとおり run から出ない、またはユーザー判断・M4 の義務。
* SigTyClosed / DeclValuePh / RecRulePhU の統合（「宣言型・値・recursor 規則の閉包性」を 1 本の環境条件にまとめる）: 3 行が 1 行に減る見かけの案だが、T1L-53 / 各行の文の強化と新しい行の作成になる。REV15 の N1-b と同型で、reviewer は強化を新規扱いとした。要ユーザー判断。
* N2-b: N2-c（コンパイラ側 `packTupleInputs` の全域化）はコンパイラ本番の編集でユーザー承認が要る。

## 注記

* 7 行（SigTyClosed ほか）の Lean は base に無く、すべて par/rt-final@378f8e31（`readerTrace_final`）または同系統の branch にある。`git log --all -S` の最古 commit: SigTyClosed 4d6b9719、InstSFieldsDet 206c39a2、DeclValuePh / PackTupleInputsBridge / RawNodePh / NormNodePh 8c4f49c9（rt25）、RecRulePhU 9e633268（rt55）。
* 台帳の行の数・文は変更していない。
