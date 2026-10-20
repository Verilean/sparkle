#!/usr/bin/env python3
"""Mechanical part of the environment-capture re-base (docs/parallel/M-env-capture-a.md).

The compiler's translator takes the environment its entry read:

    translateExprToWire env e hint top named
    translateStep env, translateFallback env, translateInstanceOrFallback env rec
    synthesizeCombinationalCoreWith (translate : Environment -> TranslateFn)

This script rewrites the proof and test files accordingly.  It only touches
CODE (comments and string literals are masked) and only TERM positions (a name
that is an item of an `unfold` / `simp only [...]` / `rw [...]` list is left).

What it does, per file of Tools/, Tests/ and scripts/shipping-coverage/:

 1. entry applications
      synthesizeCombinational(Core)With (fun a b c d => translateExprToWire a b c d)
        -> ... (fun env a b c d => translateExprToWire env a b c d)
 2. base names in term position
      translateExprToWire          -> translateExprToWire tenv
      translateStep                -> (translateStep tenv)
      translateFallback            -> (translateFallback tenv)
      translateInstanceOrFallback  -> translateInstanceOrFallback tenv
 3. CLASS II definitions (Prop-valued definitions / structures / inductives
    of the CompilerM level whose body mentions the translator): an explicit
    first parameter `(tenv : Lean.Environment)`, and `X` -> `X tenv` at every
    use.  The set is the closure, computed here, of the definitions whose
    body mentions `tenv` after step 2, minus CLASS I.
 4. CLASS I definitions (statements about MetaM runs, used at the entry
    level where the environment is the run's own read): the body gets a
    leading `forall {tenv : Lean.Environment},` (implicit; `exists (tenv ...)` for
    MachineRan), so
    their parameter lists -- and every statement that only NAMES them -- do
    not change.  Their provers / appliers are edited by hand (listed in the
    doc), not here.
 5. `variable {tenv : Lean.Environment}` after the imports of every file in
    which a theorem / example / class II definition now mentions `tenv`
    (Lean includes it in exactly the declarations whose statement mentions
    it).
 6. PROGRAM declarations (`run_cmd`, `#eval`, `def`s of Tests/, the listed
    generator functions): `let tenv <- Lean.getEnv` as the first statement
    of the declaration's first `do` block.

Everything the rules do not cover is REPORTED, not guessed (section "HAND"
of the output).  The script refuses to run on a tree that already contains
the identifier `tenv`.

Usage:  python3 scripts/env-capture/rebase.py [--dry-run] [--report FILE]
Run from the repository root, once, on the tree right after the compiler
commit.  The counts it asserts are those of poc 80745d94.
"""
import os
import re
import sys
import collections

ROOTS = ['Tools', 'Tests', 'scripts/shipping-coverage']
BASE = ['translateExprToWire', 'translateStep', 'translateFallback', 'translateInstanceOrFallback']
PAREN = {'translateStep', 'translateFallback'}

# statements about MetaM runs, quantified over the environment INSIDE
CLASS_I = ['BodyRel', 'TranslateRel', 'HarnessRel', 'FallbackRel', 'MachineCloses',
           'MachineClosesAt', 'MachineClosesAtC', 'MachineClosesAtS', 'MachineKeepsCoherent',
           'LetsClose', 'CallsClose', 'CallsPure', 'HarnessStill', 'HarnessProv',
           'MachineRan', 'MemoSound']
CLASS_I_EXISTS = {'MachineRan'}
# quantified by hand: a structure (its FIELDS), and the two statements in
# which the environment is the run's own, existential INSIDE the statement
# (`CoreVia`: after its premises; `HierConePreserves`: with the fact that it
# is a `getEnv` result).  The script reports them under HAND.
CLASS_I_HAND = ['ArmObligations', 'CoreVia', 'HierConePreserves']
# definitions that keep their statement (they do not mention the translator
# once the tag predicates are stated on reads): never made class II
KEEP = ['HardwareTagged', 'ProjEnvDefines', 'InstancePreserves', 'Instance1Preserves',
        'InstanceNPreserves', 'InstanceGPreserves', 'ProjInstancePreserves']
# program declarations outside Tests/ (file suffix, declaration name)
PROGRAMS = [('Tools/ShippingMachineCommand.lean', 'generateCore')]
# declarations the script must not touch (a local binder shadows the name)
SKIP_DECLS = [('Tests/Compiler/InlineUnfoldRegressionTest.lean', 'oldTryInline')]

DECL = re.compile(
    r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local)\s+)*'
    r'(theorem|lemma|def|abbrev|instance|example|structure|inductive|elab|macro|syntax|initialize|'
    r'run_cmd|run_meta|open|namespace|section|end|variable|set_option|import|mutual|deriving|'
    r'elab_rules|macro_rules|declare_syntax_cat|attribute|#\w+)\b')
NAMED = re.compile(r'\b(theorem|lemma|def|abbrev|instance|structure|inductive)\s+([^\s:({\[]+)')


def mask(t):
    """comments and string literals blanked, offsets preserved"""
    out = list(t)
    i, n, depth = 0, len(t), 0
    while i < n:
        if depth == 0 and t.startswith('--', i):
            j = t.find('\n', i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = ' '
            i = j
            continue
        if t.startswith('/-', i):
            depth += 1
            out[i] = out[i + 1] = ' '
            i += 2
            continue
        if depth > 0 and t.startswith('-/', i):
            depth -= 1
            out[i] = out[i + 1] = ' '
            i += 2
            continue
        if depth > 0:
            if t[i] != '\n':
                out[i] = ' '
            i += 1
            continue
        if t[i] == '"':
            j = i + 1
            while j < n and t[j] != '"':
                if t[j] == '\\':
                    j += 1
                j += 1
            for k in range(i + 1, min(j, n)):
                if out[k] != '\n':
                    out[k] = ' '
            i = j + 1
            continue
        i += 1
    return ''.join(out)


def decls(c):
    lines = c.split('\n')
    offs, o = [], 0
    for ln in lines:
        offs.append(o)
        o += len(ln) + 1
    starts = []
    for i, ln in enumerate(lines):
        m = DECL.match(ln)
        if m:
            starts.append((offs[i], m.group(1), ln))
    res = []
    for k, (s, kind, ln) in enumerate(starts):
        e = starts[k + 1][0] if k + 1 < len(starts) else len(c)
        nm = NAMED.search(ln)
        res.append((s, e, kind, nm.group(2) if nm else ''))
    return res


def sig_end(seg):
    depth, i, n = 0, 0, len(seg)
    while i < n:
        ch = seg[i]
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif depth == 0 and seg.startswith(':=', i):
            return i
        elif depth == 0 and seg.startswith('\n  | ', i):
            return i
        elif depth == 0 and seg.startswith('where', i) and not seg[i - 1].isalnum() \
                and not seg[i + 5:i + 6].isalnum():
            return i
        i += 1
    return n


def name_position(c, s, e):
    """is the name at c[s:e] an item of an unfold / simp / rw list?"""
    ls = c.rfind('\n', 0, s) + 1
    pre = c[ls:s]
    post = c[e:e + 40]
    if re.search(r'\b(unfold|delta)\s+((?:[\w.]+\s+)*)$', pre):
        return True
    if re.search(r'(\[|,)\s*(←\s*|↓\s*)?$', pre) and re.match(r'\s*(,|\])', post):
        return True
    return False


def name_rx(names):
    return re.compile(r'(?<![\w`.])((?:[A-Za-z_]\w*\.)*)(' + '|'.join(map(re.escape, names)) +
                      r')(?![\w?!\'.])')


class File:
    def __init__(self, path):
        self.path = path
        self.text = open(path).read()
        self.edits = []          # (start, end, replacement)

    def apply(self):
        if not self.edits:
            return False
        self.edits.sort()
        out, pos = [], 0
        for s, e, r in self.edits:
            assert s >= pos, (self.path, s, pos, r)
            out.append(self.text[pos:s])
            out.append(r)
            pos = e
        out.append(self.text[pos:])
        self.text = ''.join(out)
        self.edits = []
        return True


def main():
    dry = '--dry-run' in sys.argv
    report_path = None
    if '--report' in sys.argv:
        report_path = sys.argv[sys.argv.index('--report') + 1]
    files = []
    for r in ROOTS:
        for dp, _, fn in os.walk(r):
            for f in sorted(fn):
                if f.endswith('.lean'):
                    files.append(File(os.path.join(dp, f)))
    files.sort(key=lambda f: f.path)
    for f in files:
        assert not re.search(r'(?<![\w.])tenv(?![\w\'])', mask(f.text)), \
            f'{f.path}: the identifier tenv is already used'
    hand = []
    count = collections.Counter()

    def is_program(f, kind, nm):
        if kind in ('run_cmd', 'run_meta', 'elab', 'initialize') or kind.startswith('#'):
            return True
        if any(f.path.endswith(p) and nm == d for p, d in PROGRAMS):
            return True
        if kind in ('def', 'abbrev') and not f.path.startswith('Tools/'):
            return True
        return False

    def skipped(f, nm):
        return any(f.path.endswith(p) and nm == d for p, d in SKIP_DECLS)

    # ---- steps 1 and 2: entry applications and base names ----
    entry_rx = re.compile(
        r'\b(synthesizeCombinationalCoreWith|synthesizeCombinationalWith)(\s*)\(fun\s+(\w+)\s+(\w+)'
        r'\s+(\w+)\s+(\w+)\s*=>\s*((?:Sparkle\.Compiler\.Elab\.)?translateExprToWire)\s+\3\s+\4\s+\5\s+\6\)')
    base_rx = name_rx(BASE)
    for f in files:
        c = mask(f.text)
        taken = []
        for s, e, kind, nm in decls(c):
            if skipped(f, nm):
                continue
            for m in entry_rx.finditer(c, s, e):
                f.edits.append((m.start(), m.end(),
                                f'{m.group(1)}{m.group(2)}(fun env {m.group(3)} {m.group(4)} '
                                f'{m.group(5)} {m.group(6)} => {m.group(7)} env {m.group(3)} '
                                f'{m.group(4)} {m.group(5)} {m.group(6)})'))
                taken.append((m.start(), m.end()))
                count['entry application'] += 1
            for m in re.finditer(r'\b(synthesizeCombinationalCoreWith|synthesizeCombinationalWith)\b',
                                 c[s:e]):
                a = s + m.start()
                if any(x <= a < y for x, y in taken) or name_position(c, a, s + m.end()):
                    continue
                ln = c.count('\n', 0, a) + 1
                # a translator that does not depend on the environment (a test's
                # own wrapper, a local value): `X` -> `(fun _ => X)`
                b = s + m.end()
                ws = re.match(r'\s*', c[b:]).end()
                arg = None
                if is_program(f, kind, nm):
                    im = re.match(r'[a-z_][\w\']*', c[b + ws:])
                    if im:
                        arg = (b + ws, b + ws + im.end())
                    elif c[b + ws:b + ws + 1] == '(':
                        d, k = 0, b + ws
                        while k < e:
                            if c[k] in '([{⟨':
                                d += 1
                            elif c[k] in ')]}⟩':
                                d -= 1
                                if d == 0:
                                    break
                            k += 1
                        arg = (b + ws, k + 1)
                if arg:
                    f.edits.append((arg[0], arg[0], '(fun _ => '))
                    f.edits.append((arg[1], arg[1], ')'))
                    pass
                    count['entry application, constant translator'] += 1
                else:
                    hand.append(f'{f.path}:{ln}: entry applied to another translator: '
                                f'{f.text.splitlines()[ln - 1].strip()[:120]}')
            for m in base_rx.finditer(c, s, e):
                if any(x <= m.start() < y for x, y in taken):
                    continue
                if name_position(c, m.start(), m.end()):
                    count['name position (left)'] += 1
                    continue
                q, nm2 = m.group(1), m.group(2)
                ln = c.count('\n', 0, m.start()) + 1
                if q and not re.match(r'(Sparkle|Tools)\.', q):
                    hand.append(f'{f.path}:{ln}: qualified occurrence {q}{nm2}')
                    continue
                if nm2 in PAREN:
                    f.edits.append((m.start(), m.end(), f'({q}{nm2} tenv)'))
                else:
                    if re.match(r'\s*[)\],⟩]', c[m.end():m.end() + 20]):
                        hand.append(f'{f.path}:{ln}: unapplied {nm2}: '
                                    f'{f.text.splitlines()[ln - 1].strip()[:120]}')
                        continue
                    f.edits.append((m.start(), m.end(), f'{q}{nm2} tenv'))
                count[nm2] += 1
        f.apply()

    # ---- step 3: the class II closure ----
    class2 = []
    while True:
        new = []
        for f in files:
            if not f.path.startswith('Tools/'):
                continue
            c = mask(f.text)
            for s, e, kind, nm in decls(c):
                if kind not in ('def', 'structure', 'inductive', 'abbrev') or not nm:
                    continue
                if nm in CLASS_I or nm in CLASS_I_HAND or nm in KEEP or nm in class2 or nm in new:
                    continue
                if is_program(f, kind, nm) or skipped(f, nm):
                    continue
                if re.search(r'(?<![\w.])tenv(?![\w\'])', c[s:e]):
                    new.append(nm)
        if not new:
            break
        dup = [n for n in new if sum(1 for g in files for (_, _, k, m) in decls(mask(g.text))
                                     if m == n and k in ('def', 'structure', 'inductive', 'abbrev')) > 1]
        for n in dup:
            hand.append(f'class II name defined more than once: {n}')
        rx = name_rx(new)
        for f in files:
            c = mask(f.text)
            for s, e, kind, nm in decls(c):
                if skipped(f, nm):
                    continue
                for m in rx.finditer(c, s, e):
                    q, nm2 = m.group(1), m.group(2)
                    ln = c.count('\n', 0, m.start()) + 1
                    pre = c[max(0, m.start() - 40):m.start()]
                    if nm == nm2 and kind in ('def', 'structure', 'inductive', 'abbrev') and \
                            re.search(r'\b(def|structure|inductive|abbrev)\s+$', pre):
                        f.edits.append((m.end(), m.end(), ' (tenv : Lean.Environment)'))
                        count['class II header'] += 1
                        continue
                    if name_position(c, m.start(), m.end()):
                        count['name position (left)'] += 1
                        continue
                    if pre.rstrip().endswith('@'):
                        hand.append(f'{f.path}:{ln}: explicit application @{nm2}')
                        continue
                    if q and not re.match(r'(Sparkle|Tools)\.', q):
                        hand.append(f'{f.path}:{ln}: qualified occurrence {q}{nm2}')
                        continue
                    f.edits.append((m.start(), m.end(), f'{q}{nm2} tenv'))
                    count['class II use'] += 1
            f.apply()
        class2 += new

    # ---- step 4: class I bodies ----
    for f in files:
        c = mask(f.text)
        for s, e, kind, nm in decls(c):
            if kind != 'def' or nm not in CLASS_I:
                continue
            seg = c[s:e]
            se = sig_end(seg)
            assert seg.startswith(':=', se), (f.path, nm)
            m = re.match(r':=\s*', seg[se:])
            body_at = s + se + m.end()
            q = '∃' if nm in CLASS_I_EXISTS else '∀'
            assert c.startswith(q, body_at), (f.path, nm, c[body_at:body_at + 20])
            # an IMPLICIT binder for the universal ones: every application of a
            # hypothesis of such a type elaborates as before (the environment is
            # found from the run it is applied to); only the proofs that
            # INTRODUCE the statement name the new binder
            b = '(tenv : Lean.Environment)' if nm in CLASS_I_EXISTS else '{tenv : Lean.Environment}'
            f.edits.append((body_at, body_at, f'{q} {b}, '))
            count['class I body'] += 1
        f.apply()

    # ---- steps 5 and 6: binding `tenv` ----
    tok = re.compile(r'(?<![\w.])tenv(?![\w\'])')
    for f in files:
        c = mask(f.text)
        need_var = False
        for s, e, kind, nm in decls(c):
            if not tok.search(c, s, e):
                continue
            seg = c[s:e]
            if is_program(f, kind, nm):
                m = re.search(r'\bdo[ \t]*\n([ \t]*)', seg)
                ln = c.count('\n', 0, s) + 1
                if m:
                    # the indentation of the block's first line, read from the
                    # UNMASKED text (that line may be a comment)
                    at = s + m.start(1)
                    ind = re.match(r'[ \t]*', f.text[at:]).group(0)
                    f.edits.append((at, at, f'{ind}let tenv ← Lean.getEnv\n'))
                    count['program binder'] += 1
                    hand.append(f'{f.path}:{ln}: CHECK program binder inserted in {kind} {nm}')
                else:
                    hand.append(f'{f.path}:{ln}: program {kind} {nm} mentions tenv, no do block')
                continue
            if kind in ('def', 'structure', 'inductive', 'abbrev'):
                if nm in CLASS_I or nm in class2:
                    continue
                ln = c.count('\n', 0, s) + 1
                hand.append(f'{f.path}:{ln}: {kind} {nm} mentions tenv (class I by hand?)')
                continue
            se = sig_end(seg)
            if tok.search(seg[:se]):
                need_var = True
            else:
                ln = c.count('\n', 0, s) + 1
                hand.append(f'{f.path}:{ln}: {kind} {nm}: tenv in the proof only '
                            f'({len(tok.findall(seg[se:]))}x) -- bind it by hand')
            if re.search(r'\b(synthesizeCombinationalCore|synthesizeCombinational|synthesizeChild)\b',
                         seg[:se]) and tok.search(seg[:se]):
                ln = c.count('\n', 0, s) + 1
                hand.append(f'{f.path}:{ln}: {kind} {nm}: ENTRY-LEVEL statement mentions tenv')
        for s, e, kind, nm in decls(c):
            if kind in ('def', 'structure', 'inductive', 'abbrev') and nm in class2:
                need_var = need_var or False
        if need_var:
            last = None
            for m in re.finditer(r'^import[^\n]*\n', c, re.M):
                last = m
            at = last.end() if last else 0
            f.edits.append((at, at, '\nvariable {tenv : Lean.Environment}\n'))
            count['variable line'] += 1
        f.apply()

    changed = 0
    for f in files:
        if f.text != open(f.path).read():
            changed += 1
            if not dry:
                open(f.path, 'w').write(f.text)
    lines = ['COUNTS'] + [f'  {k}: {v}' for k, v in sorted(count.items())]
    lines += [f'  files changed: {changed}', 'CLASS II (closure)'] + [f'  {n}' for n in class2]
    lines += ['HAND'] + [f'  {h}' for h in hand]
    out = '\n'.join(lines) + '\n'
    if report_path:
        open(report_path, 'w').write(out)
    else:
        sys.stdout.write(out)


if __name__ == '__main__':
    main()
