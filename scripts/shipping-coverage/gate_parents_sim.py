#!/usr/bin/env python3
"""Derive the gate-parent writer simulation from the tree's own module_name_sim.

WRITTEN, NOT RUN (`fix/env-capture-a`).  The stimulus, the test bench text and
the comparison of `scripts/shipping-coverage/module_name_sim.{lean,sh}` are
used VERBATIM (they are built and have run); this script only swaps the
declarations: the import, the source functions, the rows, the output
directory and the `#writeVerilogDesign` lines.  Every replacement is asserted
on the template text of the tree it runs in, so a template that has moved
makes the derivation fail loudly instead of producing another program.

Usage (called by gate_parents_sim.sh):  gate_parents_sim.py <out-dir>
Writes <out-dir>/gate_parents_sim.lean and <out-dir>/gate_parents_sim_run.sh.
"""
import sys

OUT = sys.argv[1]
H = 'Sparkle.Tests.Compiler.ShippingHierarchySoundnessTest'
P = 'Sparkle.Tests.Compiler.SlotlessParentProbeTest'
# tag, declaration, source expression at (off, t) as a Nat
ROWS = [
    ('parentUse', f'{H}.parentUse',
     f'((@{H}.parentUse defaultDomain (v8S 0 off) (v8S 1 off)).val t).toNat'),
    ('wrapAdd', f'{H}.wrapAdd', f'(({H}.wrapAdd (v8S 0 off) (v8S 1 off)).val t).toNat'),
    ('parentMix', f'{H}.parentMix',
     f'((@{H}.parentMix defaultDomain (v8S 0 off) (v8S 1 off)).val t).toNat'),
    ('parentTwoCalls', f'{H}.parentTwoCalls',
     f'((@{H}.parentTwoCalls defaultDomain (v8S 0 off) (v8S 1 off)).val t).toNat'),
    ('parentRepeat', f'{H}.parentRepeat',
     f'((@{H}.parentRepeat defaultDomain (v8S 0 off) (v8S 1 off)).val t).toNat'),
    ('parentCmp', f'{H}.parentCmp',
     f'(if (@{H}.parentCmp defaultDomain (v8S 0 off) (v8S 1 off)).val t then 1 else 0)'),
    ('parentNested', f'{H}.parentNested',
     f'((@{H}.parentNested defaultDomain (v8S 0 off) (v8S 1 off)).val t).toNat'),
    ('wrapPick', f'{P}.wrapPick', f'(({P}.wrapPick (v2S 0 off) (v8S 1 off)).val t).toNat'),
]


def one(t, old, new):
    assert t.count(old) == 1, (old[:60], t.count(old))
    return t.replace(old, new)


def main():
    t = open('scripts/shipping-coverage/module_name_sim.lean').read()
    t = one(t, 'import Tests.Compiler.CacheCoherenceProbe\n',
            'import Tests.Compiler.SlotlessParentProbeTest\nimport Tests.Compiler.CallWidthHuntTest\n')
    t = one(t, 'open Tests.Compiler.CacheCoherenceProbe\n', '')
    a = t.index('def srcNTop ')
    b = t.index('structure Row where')
    src = ('def v2S (i off : Nat) : Signal defaultDomain (BitVec 2) :=\n'
           '  ⟨fun t => BitVec.ofNat 2 (vval 2 i (off + t))⟩\n\n')
    for tag, decl, expr in ROWS:
        src += f'def src_{tag} (off t : Nat) : Nat := {expr}\n\n'
    t = t[:a] + src + t[b:]
    a = t.index('def rows : List Row :=')
    b = t.index('structure Cyc where')
    rows = 'def rows : List Row :=\n  [ ' + ',\n    '.join(
        f'{{ tag := "{tag}", decl := `{decl}, src := src_{tag} }}' for tag, decl, _ in ROWS) + ' ]\n\n'
    t = t[:a] + rows + t[b:]
    assert t.count('module-name-sim') >= 2
    t = t.replace('module-name-sim', 'gate-parents-sim').replace('MODNAMESIM', 'GATEPARENTSIM')
    a = t.index('#writeVerilogDesign ')
    t = t[:a] + ''.join(
        f'#writeVerilogDesign {decl} ".lake/build/gen/gate-parents-sim/{tag}_cmd.sv"\n'
        for tag, decl, _ in ROWS)
    open(f'{OUT}/gate_parents_sim.lean', 'w').write(t)

    s = open('scripts/shipping-coverage/module_name_sim.sh').read()
    s = one(s, 'cd "$(dirname "$0")/../.."\n', ': # already at the repository root\n')
    s = one(s, 'scripts/shipping-coverage/module_name_sim.lean', f'{OUT}/gate_parents_sim.lean')
    s = s.replace('module-name-sim', 'gate-parents-sim').replace('MODNAMESIM', 'GATEPARENTSIM')
    open(f'{OUT}/gate_parents_sim_run.sh', 'w').write(s)


if __name__ == '__main__':
    main()
