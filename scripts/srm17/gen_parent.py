#!/usr/bin/env python3
"""Generates the declarations of Tests/Compiler/Srm17ParentTest.lean that depend on SRM16's statements.  Reads ONLY Tests/Compiler/Srm16ParentTest.lean (the `_viaResetState` SOURCE statements).
Substitution/deletion list (per source statement `topshareX_Y_viaResetState`):
  D1: delete the four binders `hIUraw`, `hIU`, `hAg`, `hRd` (their Prop text is KEPT, verbatim, as the conclusion of `topshareX_hIUraw` ... `topshareX_hRd`);
  S1: rename `_viaResetState` to `_viaResetSrc`;
  S2: the proof calls the SOURCE theorem with the four residuals supplied by `topshareX_{hIUraw,hIU,hAg,hRd}` at the position of the deleted binders.
Prints Lean text to stdout."""
import re, sys
src = open('Tests/Compiler/Srm16ParentTest.lean').read()
blocks = re.findall(r'(theorem \w+_viaResetState .*?)(?=\n\ntheorem |\n\nend |\nend )', src, re.S)
assert len(blocks) == 4, len(blocks)
RES = ['hIUraw', 'hIU', 'hAg', 'hRd']

def split_stmt(blk):
    """binders at bracket depth 0 of the header, each as its source text; the conclusion after the final top-level ` :`"""
    stmt = blk.split(':= by')[0].rstrip()
    name = re.match(r'theorem (\w+)', stmt).group(1)
    hdr = stmt[len('theorem ' + name):]
    depth, start, binders = 0, None, []
    concl = None
    for k, ch in enumerate(hdr):
        if ch in '({[':
            if depth == 0: start = k
            depth += 1
        elif ch in ')}]':
            depth -= 1
            if depth == 0: binders.append(hdr[start:k + 1])
        elif ch == ':' and depth == 0:
            concl = hdr[k + 1:].strip()
            break
    return name, binders, concl

def bname(g):
    m = re.match(r"[\({]([\w' ]+?) :", g)
    return m.group(1).strip() if m else None

out, spec = [], {}
for blk in blocks:
    name, groups, concl = split_stmt(blk)
    design = name.split('_')[0]            # topshareM / topshareQ
    names = [bname(g) for g in groups]
    ires = {nm: g for nm, g in zip(names, groups) if nm in RES}
    assert set(ires) == set(RES), ires.keys()
    kept = [g for nm, g in zip(names, groups) if nm not in RES]
    upto = groups[:names.index('hw') + 1]
    if design not in spec:
        spec[design] = True
        proof = open('scripts/srm17/proof_%s.txt' % design[-1]).read()
        ub = ' ' + ' '.join(upto)
        exp = [bname(g) for g in upto if g.startswith('(')]
        call = design + '_modP ' + ' '.join(exp)
        out.append('/-- **`ModP` for `%s`**: the run\'s module `raw` and every module of `D.modules` (a `ChildP` recursion over the callees, `ran_designP`). -/\ntheorem %s_modP%s :\n    ModP raw ∧ ∀ g ∈ D.modules, ModP g := by\n%s' % (design, design, ub, proof))
        def prop(g):
            nm = bname(g)
            t = re.sub(r"^\(%s : " % nm, '', g)
            assert t.rstrip().endswith(')')
            return t.rstrip()[:-1]
        out.append('theorem %s_hIUraw%s :\n    %s :=\n  (%s).1.iu\n' % (design, ub, prop(ires['hIUraw']).strip(), call.replace(design + '_modP', '(' + design + '_modP') + ')'))
        out.append('theorem %s_hIU%s :\n    %s :=\n  fun m hm => ((%s).2 m hm).iu\n' % (design, ub, prop(ires['hIU']).strip(), call.replace(design + '_modP', design + '_modP')))
        out.append('theorem %s_hAg%s :\n    %s :=\n  fun m hm => ((%s).2 m hm).ag\n' % (design, ub, prop(ires['hAg']).strip(), call))
        out.append('theorem %s_hRd%s :\n    %s :=\n  fun m hm => ((%s).2 m hm).rd\n' % (design, ub, prop(ires['hRd']).strip(), call))
    newname = name.replace('_viaResetState', '_viaResetSrc')
    stmt = 'theorem ' + newname + ' ' + '\n    '.join(kept) + ' :\n    ' + concl
    exp_all = [nm for g, nm in zip(groups, names) if g.startswith('(')]
    args = []
    for nm in exp_all:
        if nm == 'hIUraw': args.append('(%s_hIUraw %s)' % (design, ' '.join(bname(g) for g in upto if g.startswith('('))))
        elif nm == 'hIU': args.append('(%s_hIU %s)' % (design, ' '.join(bname(g) for g in upto if g.startswith('('))))
        elif nm == 'hAg': args.append('(%s_hAg %s)' % (design, ' '.join(bname(g) for g in upto if g.startswith('('))))
        elif nm == 'hRd': args.append('(%s_hRd %s)' % (design, ' '.join(bname(g) for g in upto if g.startswith('('))))
        else: args.append(nm)
    out.append(stmt + ' :=\n  %s %s\n' % (name, ' '.join(args)))
print('\n'.join(out))
