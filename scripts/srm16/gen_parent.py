#!/usr/bin/env python3
"""Generates Tests/Compiler/Srm16ParentTest.lean's corollary statements from the SRM13 `_viaReset` SOURCE statements
(reads only Tests/Compiler/Srm13ParentTest.lean).  Substitution/deletion list:
  A (`_viaResetO`): delete the `hO` binder.
  B (`_viaResetState`): delete the `hO` and `hrk` binders; insert at hrk's position
      hsk, hIUraw, hIU, hAg, hRd.
Prints Lean text to stdout."""
import re, sys
src = open('Tests/Compiler/Srm13ParentTest.lean').read()
blocks = re.findall(r'(theorem \w+_viaReset .*?)(?=\n\ntheorem |\nend )', src, re.S)
assert len(blocks) == 4, len(blocks)
STRUCT = '''    (hIUraw : ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ raw.body → Stmt.inst mn' i c' ∈ raw.body → mn = mn')
    (hIU : ∀ m ∈ D.modules, ∀ (mn i : String) (c : List (String × Expr)) (mn' : String) (c' : List (String × Expr)),
      Stmt.inst mn i c ∈ m.body → Stmt.inst mn' i c' ∈ m.body → mn = mn')
    (hAg : ∀ m ∈ D.modules, ∀ r c rs inp (init : Int) c' rs' inp' (init' : Int),
      Stmt.register r c rs inp init ∈ m.body → Stmt.register r c' rs' inp' init' ∈ m.body → init.toNat = init'.toNat)
    (hRd : ∀ m ∈ D.modules, ∀ nm aw dw c wa wd we ra rd cr ew er,
      Stmt.memory nm aw dw c wa wd we ra rd cr ew er ∈ m.body →
      ∀ c' rs' inp' (init' : Int), Stmt.register rd c' rs' inp' init' ∈ m.body → init'.toNat = 0)'''
out = []
for blk in blocks:
    name = re.match(r'theorem (\w+)', blk).group(1)
    stmt = blk.split(':= by')[0] if ':= by' in blk else blk.split(' :=\n')[0]
    stmt = stmt.rstrip()
    lines = stmt.split('\n')
    # explicit binder names: "(name :" at bracket depth 0 of the header (after the theorem name)
    names = []
    hdr = stmt[len('theorem ' + name):]
    depth = 0
    for k, ch in enumerate(hdr):
        if ch in '({[':
            if ch == '(' and depth == 0:
                m = re.match(r"\(([\w']+) :", hdr[k:])
                if m: names.append(m.group(1))
            depth += 1
        elif ch in ')}]':
            depth -= 1
        if ch == ':' and depth == 0: break
    N = re.search(r'ResetNk (\d) raw D s.kids', stmt).group(1)
    def drop(stmt, hdr):
        res, skip = [], False
        for ln in stmt.split('\n'):
            if ln.strip().startswith(hdr): continue
            res.append(ln)
        return '\n'.join(res)
    base = name.replace('_viaReset', '')
    # A
    a = drop(stmt, '(hO :').replace(name, base + '_viaResetO')
    argsA = ' '.join(names)
    out.append(a + ' := by\n  have hO := %s_hO %s\n  exact %s %s\n' % (
        base.split('_')[0], 'O T hA ' + ' '.join(n for n in names if n.startswith('entry') or n in ('hR0','hcl')) + ' hcore hpost hw', name, argsA))
    # B
    b = drop(stmt, '(hO :')
    b = '\n'.join(('(hsk : s.kids = Tools.ShippingSrm16Reset.resetKids D %s raw)\n' % N + STRUCT) if ln.strip().startswith('(hrk :') else ln for ln in b.split('\n'))
    b = b.replace('(hsk', '    (hsk').replace(name, base + '_viaResetState')
    namesB = [n for n in names if n not in ('hO',)]
    call = ' '.join(namesB)
    out.append(b + ' := by\n  have hrk : Tools.ShippingMachineShipsDepth.ResetNk %s raw D s.kids := by\n    rw [hsk]\n    exact Tools.ShippingSrm16Reset.resetNk_resetKids %s raw D hIUraw hIU hAg hRd\n  exact %s_viaResetO %s\n' % (
        N, N, base, ' '.join(n for n in names if n != 'hO')))
print('\n'.join(out))
