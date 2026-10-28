#!/usr/bin/env python3
"""Generates the `_viaStartNk` corollaries of Tests/Compiler/Srm18ParentTest.lean.  Reads ONLY the SRM17 `_viaResetSrc` SOURCE statements (Tests/Compiler/Srm17ParentTest.lean).
Substitution/deletion list (per source statement `topshareX_Y_viaResetSrc`, depth N = 2 for M, 1 for Q):
  S1: rename `_viaResetSrc` to `_viaStartNk`;
  S2: binder `(s : KState (KT N))` replaced by the three binders `(st0 : String → Nat) (mems : Sparkle.IR.Semantics.MEnv) (kids : String → KT N)`;
  S3: binder `(hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D N raw)` replaced, AT THE SAME POSITION, by `(hRK : Tools.ShippingMachineShipsDepth.ResetNk N raw D kids)`;
  S4: in the remaining text `s.st` -> `st0`, `s.kids` -> `kids`, and every other standalone token `s` -> `(⟨st0, mems, kids⟩ : KState (KT N))`;
  proof: SRM16 `_viaResetO` (called) at the corresponding arguments, `hRK` at the position of its `hrk`.
Prints Lean text to stdout."""
import re
src = open('Tests/Compiler/Srm17ParentTest.lean').read()
blocks = re.findall(r'(theorem \w+_viaResetSrc .*?)(?=\n\ntheorem |\n\n/--|\n\nend |\nend )', src, re.S)
assert len(blocks) == 4, len(blocks)
def split_stmt(blk):
    stmt = blk.split(' :=\n')[0].rstrip()
    name = re.match(r'theorem (\w+)', stmt).group(1)
    hdr = stmt[len('theorem ' + name):]
    depth, start, binders, concl = 0, None, [], None
    for k, ch in enumerate(hdr):
        if ch in '({[':
            if depth == 0: start = k
            depth += 1
        elif ch in ')}]':
            depth -= 1
            if depth == 0: binders.append(hdr[start:k + 1])
        elif ch == ':' and depth == 0:
            concl = hdr[k + 1:].strip(); break
    return name, binders, concl
def bname(g):
    m = re.match(r"[\({]([\w' ₀-₉]+?) :", g)
    return m.group(1).strip() if m else None
out = []
for blk in blocks:
    name, groups, concl = split_stmt(blk)
    N = 2 if name.startswith('topshareM') else 1
    anon = '(⟨st0, mems, kids⟩ : KState (KT %d))' % N
    def sub(t):
        t = t.replace('s.st', 'st0').replace('s.kids', 'kids')
        return re.sub(r"(?<![\w'.])s(?![\w'.₀-₉])", anon, t)
    new = []
    names = [bname(g) for g in groups]
    for g, nm in zip(groups, names):
        if nm == 's':
            assert g == '(s : KState (KT %d))' % N, g
            new.append('(st0 : String → Nat) (mems : Sparkle.IR.Semantics.MEnv) (kids : String → KT %d)' % N)
        elif nm == 'hsk':
            assert g == '(hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D %d raw)' % N, g
            new.append('(hRK : Tools.ShippingMachineShipsDepth.ResetNk %d raw D kids)' % N)
        else:
            new.append(sub(g))
    newname = name.replace('_viaResetSrc', '_viaStartNk')
    stmt = 'theorem ' + newname + ' ' + '\n    '.join(new) + ' :\n    ' + sub(concl)
    args = []
    for g, nm in zip(groups, names):
        if not g.startswith('('): continue
        if nm == 's': args.append(anon)
        elif nm == 'hsk': args.append('hRK')
        else: args.append(nm)
    callee = name.replace('_viaResetSrc', '_viaResetO')
    out.append(stmt + ' :=\n  %s %s\n' % (callee, ' '.join(args)))
print('\n'.join(out))
