# `#sim` and the design artifact (paper only; next unit)

Round par/a-1, worker A. Nothing here is implemented or built. Sources read:
`Sparkle/Compiler/Elab.lean` 9203–9330 (`#sim`), `Sparkle/Backend/CSim.lean`
2468–2500, 2611–2665, 2813–2818 (`toCJIT`), `Sparkle/Core/SimVerilator.lean`
129–151, `Sparkle/Backend/VerilogDesign.lean`.

## What `#sim` does today (NOT switched; outside the guarantee)

    let design    ← synthesizeHierarchical declName
    let optimized := optimizeDesign design            -- every module: optimizeModule, unchecked
    let jitC      := toCJIT optimized                 -- the JIT C
    let verilog   := toVerilogDesign optimized        -- every module: optimizeModule AGAIN
    let m         := optimized.modules.find? (·.name == toString declName)  -- else the last module
    userInputs := m.inputs.filter (!isSimClkRst ·.name) ; outputs := m.outputs ; topName := m.name

So `#sim` uses THREE modules for one top, none of which is the endpoints'
`checkedOptimize b`:

| consumer | top module |
|---|---|
| `.sv` for `loadVerilator` | `optimizeModule (optimizeModule b)` (children likewise, twice) |
| JIT C (`toCJIT`) | `optimizeModule b`, found by `optimized.topModule` |
| `SimInput` / `SimOutput` / port specs / indices | `optimizeModule b`, found by NAME `toString declName` (fallback: last module) |

The optimizer is idempotent on every module of only 5 of 37 measured designs
(status log, finding D). The design endpoints say nothing about any of the
three. Until the unit below is done, `#sim` (both `load` and `loadVerilator`)
is to be stated as outside the guarantee.

## The unit: one artifact for `#sim`

Let `A := designArtifact design` (`Sparkle.Backend.Verilog`: the module named
`design.topModule` through `checkedOptimize`, the others as they are) and
`dA := { design with modules := A }`.

Change (three lines of `#sim`):

    let verilog := toVerilogDesignChecked design      -- = join of emitModule over A
    let jitC    := toCJIT dA                          -- the JIT C of the SAME modules
    let m       := the module of A named design.topModule   -- = checkedOptimize b

### Facts this needs (none is proved in the form stated)

1. **Ports of the shipped top, unconditionally.**

       checkedOptimize_ports (m) :
         (checkedOptimize m).inputs = m.inputs ∧ (checkedOptimize m).outputs = m.outputs

   Today: `checkedOptimize_name` is unconditional
   (`Tools/ShippingModuleNames.lean` 87); `checkedOptimize_inputs` holds under
   `hierBinds` only (`Tools/ShippingHierShipsSV.lean` 34);
   `Tools.ShippingOptSoundness.checkedOptimize_ports` under `simpleBody` only.
   Branch by branch: `optCheck` / `refineCheck` accept only with
   `o.inputs = m.inputs` and `o.outputs = m.outputs` (conjuncts of the checks);
   `deinline` is `m` or `{ o with body, wires }`; the fallbacks return `m`;
   the last branch (`else o`, memories and other statement kinds) needs

       optimizeModule_ports (m) :
         (optimizeModule m).inputs = m.inputs ∧ (optimizeModule m).outputs = m.outputs

   which is by unfolding (`eliminateZeroBits` and the final record are
   `{ m with body, wires }`; the primitive branch is `m`) — the pattern of the
   `hn` step inside `checkedOptimize_name`.
   USE: `SimInput` / `SimOutput` fields, their widths and the positional
   indices (`JIT.setInput idx`, `JIT.getOutput slot`) are computed from the
   port LISTS; with fact 1 they are those of the full entry's `b`, so the
   typed wrapper does not change when the artifact does.

2. **One top lookup.** `#sim` finds the top by `toString declName`,
   `designArtifact` and `toCJIT` by `design.topModule`. Needed:

       design.topModule = b.name            (the writer theorem's premise `htop`,
                                             measured true on 37 of 37)
       b.name = toString declName           (census column `topName`; not a theorem)

   or, simpler, `#sim` looks the top up by `design.topModule` like the other
   two (then only `htop` is used, and the "fallback: last module" arm goes).

3. **The JIT's input index map against the wrapper's.** Independent of the
   artifact, but it is the fact that makes fact 1 usable: `#sim` numbers
   `m.inputs.filter (!isSimClkRst ·.name)` (drops `clk`, `rst`, `reset`,
   `*_clk`, `*_rst`, …) from 0, while `emitSetInputSwitch` numbers
   `m.inputs.filter (·.name != "clk")` (drops `clk` ONLY; wide ports take
   several slots). The two numberings agree only when no dropped-by-`#sim`
   port other than `clk` precedes a user input and no input is wider than
   64 bits. As a statement:

       ∀ k p, userInputs[k]? = some p →
         slotOf (m.inputs.filter (·.name != "clk")) p = k

   (false in general: `rst` before a user input shifts the JIT's indices).
   This is a property of the two filters on the port list of fact 1; it
   should be DECIDED per declaration by `#sim` (an error otherwise), not
   assumed.

4. **Names read at run time.** `toCJIT` keeps as struct members the wires
   feeding registers and every `_gen_*` wire of the top
   (`collectTickRefWires`, `genWires`), and drivers read wires by name
   (`JIT.resolveWires`). With `dA` the top's wire list is that of
   `checkedOptimize b`: `b`'s own (fallback), a superset of
   `optimizeModule b`'s (`deinlineRaw`: `m.wires.filter (o.wires.contains ·
   || named)`), or `optimizeModule b`'s (accepted, last branch). A name
   that exists today exists after the change; indices of `jit_get_wire`
   may shift (they are resolved by name).

### What the unit would and would NOT give

* It gives: the `.sv` `loadVerilator` builds IS the text the writer prints
  and `writer_prints_endpoint_artifact` speaks about; the JIT C is generated
  from the same module list; the typed wrapper's ports are the full entry's.
* It does NOT give a statement about the JIT C's behaviour: no theorem
  relates `toCJIT`'s C to `runModule`. The CSim / JIT backend stays
  outside the guarantee after the unit; what changes is that it is fed the
  proved artifact instead of a second, unchecked optimization of it.
* Cost to measure before adopting: children enter the JIT unoptimized
  (text of the children 49358 against 25348 characters on the 37 measured
  designs); the JIT tests of the RV32 SoC and the H.264 pipelines time
  their runs.
* `#writeDesign` has the same split today: its `.sv` is the artifact, its C
  simulation and JIT wrapper are `toCDesign` / `toCJIT` of
  `optimizeDesign design` (with the observable wires). The same unit
  applies to it.

### Order of work

1. `optimizeModule_ports`, `checkedOptimize_ports` (pure, small).
2. `#sim`: top by `design.topModule`; the decidable index agreement of
   fact 3 as a check with an error message; `.sv` by
   `toVerilogDesignChecked`.
3. Measure the existing `#sim` users with the JIT on `dA`
   (`Tests/IP/Control/ControlJITTest.lean` and the limited simulation
   `scripts/shipping-coverage/writer_sim.sh` extended with a `loadVerilator`
   row); only then switch the JIT.
