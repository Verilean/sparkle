#!/usr/bin/env python3
"""SRM6 B1: inventory of declarations in Tools/*.lean that mention designCheck / kidsPass / kidCheck.

TEXT-LEVEL scan (declaration = from a line starting with theorem/lemma/def/abbrev/instance/structure up to the next one);
NOT elaborated: a hit inside a comment/docstring is stripped, a use through an unfolded alias is not seen.
Usage: python3 scripts/srm6/inventory.py [Tools-dir] > scripts/srm6/inventory.tsv ; summary on stderr.
Columns: file, line, kind, name, role, uses, depth, class
 role   : PRODUCER  (the statement CONCLUDES a designCheck/kidsPass/kidCheck = true)
          TRANSFORMER (takes one as hypothesis AND concludes one)
          CONSUMER  (the statement takes one as hypothesis, or the body unfolds/uses one)
          DEF       (a def/abbrev whose body mentions one)
 uses   : conjuncts used (text = textCheckI/textCheckI_sound; inst = kidsPass_at / instance resolution (Resolved, childMap);
          kid = kid recursion (kidsPass_at feeding the IH or a kid check); leaf = leafCheck/leaf_forward/leaf_backward; eq = unfolds designCheck/kidCheck/kidsPass)
 depth  : U = statement/body ties the check to the uniform depth `n` of KSn/DesignSV/SVBounds/InvN/Nat.rec (induction, `n + 1`, `KSn`);  - otherwise
 class  : A = uses only facts hcheck also gives (text/inst/leaf of ONE level, no depth tie)  -> restatable as is
          B = needs the uniform depth (depth = U)
          C = unclear (rule cannot decide; read by hand)   P = producer (replaced by SRM5's hcheck producers, not a consumer to restate)
"""
import re, sys, glob, os
root = sys.argv[1] if len(sys.argv) > 1 else 'Tools'
KEY = re.compile(r'\b(designCheck\w*|kidsPass\w*|kidCheck\w*)')
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(theorem|lemma|def|abbrev|instance|structure)\s+([^\s:({\[]+)?')

def strip(src):
    src = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
    return re.sub(r'--[^\n]*', '', src)

rows = []
for path in sorted(glob.glob(os.path.join(root, '*.lean'))):
    if 'Srm5' in path or 'Srm6' in path:  # SRM5/6 files are the replacement, not the inventory
        continue
    raw = open(path, encoding='utf8').read()
    lines = strip(raw).split('\n')
    starts = [i for i, l in enumerate(lines) if DECL.match(l)]
    starts.append(len(lines))
    for a, b in zip(starts, starts[1:]):
        txt = '\n'.join(lines[a:b])
        if not KEY.search(txt):
            continue
        m = DECL.match(lines[a])
        kind, name = m.group(1), m.group(2) or '?'
        k = txt.find(':=')
        sig, body = (txt[:k], txt[k:]) if k >= 0 else (txt, '')
        # split the signature at the LAST top-level ':' (paren/brace/bracket depth 0): binders | conclusion
        depth_, cut = 0, -1
        for i, ch in enumerate(sig):
            if ch in '([{⟨': depth_ += 1
            elif ch in ')]}⟩': depth_ -= 1
            elif ch == ':' and depth_ == 0 and sig[i+1:i+2] != '=': cut = i
        binders, concl_txt = (sig[:cut], sig[cut+1:]) if cut >= 0 else (sig, '')
        # hypotheses can also sit in the conclusion as `A → B → goal`
        parts = concl_txt.split('→')
        goal = parts[-1]
        hyp = bool(KEY.search(binders)) or any(KEY.search(x) for x in parts[:-1])
        concl = bool(KEY.search(goal))
        if kind in ('def', 'abbrev', 'structure', 'instance'):
            role = 'DEF'
        elif concl and hyp:
            role = 'TRANSFORMER'
        elif concl:
            role = 'PRODUCER'
        else:
            role = 'CONSUMER'
        uses = []
        if re.search(r'textCheckI', txt): uses.append('text')
        if re.search(r'kidsPass_at|Resolved|childMap_some|instOk', txt): uses.append('inst')
        if re.search(r'kidsPass_at|kidCheck|kidsPass', txt): uses.append('kid')
        if re.search(r'leafCheck|leaf_forward|leaf_backward|leaf_outs|outsLeaf', txt): uses.append('leaf')
        if re.search(r'simp only \[[^\]]*(designCheck|kidCheck|kidsPass)|unfold (designCheck|kidCheck|kidsPass)|designCheck_eq|rw \[designCheck|cases m <;> simp only \[designCheck', txt): uses.append('eq')
        depth = '-'
        if re.search(r'\bKSn\b|\bDesignSV\b|\bSVBounds\b|\bInvN\b|induction\s+\w+|Nat\.rec|\b\w+\s*\+\s*1\b.*designCheck|designCheck\s+\S+\s*\(?\w+\s*\+\s*1', txt):
            depth = 'U'
        if role == 'PRODUCER': cls = 'P'
        elif depth == 'U': cls = 'B'
        elif uses and set(uses) <= {'text', 'inst', 'kid', 'leaf', 'eq'} and ('text' in uses or 'leaf' in uses or 'inst' in uses): cls = 'A'
        else: cls = 'C'
        rows.append((os.path.basename(path), a + 1, kind, name, role, '+'.join(uses) or '-', depth, cls))

print('file\tline\tkind\tname\trole\tuses\tdepth\tclass')
for r in rows:
    print('\t'.join(map(str, r)))
from collections import Counter
c = Counter((r[4], r[7]) for r in rows)
sys.stderr.write('files with hits: %d; declarations: %d\n' % (len({r[0] for r in rows}), len(rows)))
for k, v in sorted(c.items()):
    sys.stderr.write('  %s %s: %d\n' % (k[0], k[1], v))
