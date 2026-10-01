#!/usr/bin/env python3
"""Reports for scripts/shipping-coverage/run.sh."""
import collections, re, sys

mode, work = sys.argv[1], sys.argv[2]


def is_certification_test(decl):
    return decl.startswith('Sparkle.Tests.Compiler.Shipping')


def read_routes():
    route = {}
    for line in open(f'{work}/profile.log', errors='replace'):
        m = re.match(r'\[profile\] synthesizeCombinational (\S+) (.*)', line.strip())
        if not m:
            continue
        decl, what = m.group(1), m.group(2)
        if what == 'certified front end':
            r = 'S0'
        elif what == 'mixed certified front end':
            r = 'mixed'
        elif what == 'MEMO HIT':
            r = 'memo'
        elif what.startswith('starting'):
            r = 'legacy'
        else:
            continue
        route.setdefault(decl, collections.Counter())[r] += 1
    return route


def routes():
    route = read_routes()
    tab = collections.defaultdict(collections.Counter)
    legacy = []
    for decl, c in sorted(route.items()):
        rs = set(c) - {'memo'}
        if rs & {'S0', 'mixed'}:
            kind = 'certified front end'
        elif 'legacy' in rs:
            kind = 'legacy only'
        else:
            kind = 'memo only'
        group = 'certification tests' if is_certification_test(decl) else 'real corpus'
        tab[group][kind] += 1
        if group == 'real corpus' and kind != 'certified front end':
            legacy.append(decl)
    status = collections.Counter(l.split()[-1] for l in open(f'{work}/status.txt'))
    print('files run:', sum(status.values()), 'ok:', status.get('0', 0),
          'failed:', sum(v for k, v in status.items() if k != '0'))
    for group, c in tab.items():
        print(f'{group}: {dict(c)} (total {sum(c.values())})')
    open(f'{work}/legacy_decls.txt', 'w').write('\n'.join(legacy) + '\n')


def category(head):
    if head in ('let', 'fun'):
        return head
    if head.endswith('.proj'):
        return 'structure projection'
    if 'Signal.loop' in head:
        return 'Signal.loop'
    if re.search(r'bundle|Prod\.|proj\d|unbundle', head):
        return 'tuples (bundle / Prod / proj)'
    if head in ('Functor.map', 'Seq.seq', 'Applicative.toSeq', 'Pure.pure', 'Bind.bind'):
        return 'applicative / monadic lifting'
    if 'runCircuit' in head or 'Circuit' in head:
        return 'circuit-do runtime'
    if head.startswith(('Sparkle.Core.', 'BitVec.')) or head.split('.')[0] in (
            'Nat', 'Bool', 'Fin', 'ite', 'dite', 'Neg', 'Complement', 'List', 'Array',
            'Unit', 'PUnit', 'HAppend', 'Monad', 'Applicative', 'id', 'cond'):
        return head
    return 'user definition / structure (inlined by the legacy front end)'


def reasons():
    seen = {}
    for line in open(f'{work}/cov_reasons.txt'):
        p = line.rstrip('\n').split('\t')
        if len(p) == 3:
            seen.setdefault(p[0], (p[1], p[2]))
    legacy = [l.strip() for l in open(f'{work}/legacy_decls.txt') if l.strip()]
    binders, scalar, cats, sole = (collections.Counter() for _ in range(4))
    vocabulary_only = with_instances = 0
    for decl in legacy:
        if decl not in seen:
            continue
        sc, r = seen[decl]
        scalar[sc] += 1
        if r.startswith('BINDER:'):
            binders[r[7:]] += 1
            continue
        body = r[5:]
        if body.endswith(' +instances'):
            with_instances += 1
            body = body[:-len(' +instances')]
        if body == '(vocabulary only)':
            vocabulary_only += 1
            continue
        cs = {category(h) for h in body.split(',')}
        for c in cs:
            cats[c] += 1
        if len(cs) == 1:
            sole[next(iter(cs))] += 1
    print('legacy-only real declarations:', len(legacy), 'classified:', len(seen) and
          sum(1 for d in legacy if d in seen))
    print('result type:', dict(scalar))
    print('rejected at a binder:', sum(binders.values()), binders.most_common(8))
    print('certified vocabulary only, shape rejected:', vocabulary_only,
          '| bodies with instance calls:', with_instances)
    print('features outside the certified vocabulary (declarations containing):')
    for c, n in cats.most_common(30):
        print(f'  {n:4d}  {c}')
    print('sole blocker:')
    for c, n in sole.most_common(12):
        print(f'  {n:4d}  {c}')


def feature(head):
    """Coarse feature of one residual head constant, for the blocker sets."""
    if head in ('let', 'fun'):
        return head
    if head.endswith('.proj'):
        return 'struct'
    if 'Signal.loop' in head or head.endswith('.loop'):
        return 'loop'
    if re.search(r'bundle|Prod\.|proj\d|unbundle|Signal\.fst|Signal\.snd', head):
        return 'tuple'
    if head in ('Functor.map', 'Seq.seq', 'Applicative.toSeq', 'Pure.pure', 'Bind.bind',
                'Monad.toApplicative', 'Monad.toBind', 'Applicative.toPure',
                'Applicative.toFunctor', 'Sparkle.Core.Signal.Signal.ap', 'bne', 'not',
                'and', 'or', 'Neg.neg') or re.match(
                    r'(Bool|BitVec)\.(not|and|or|xor|ule|ult|slt|sle|zero|add|sub|mul|neg|'
                    r'shiftLeft|ushiftRight|signExtend|zeroExtend|ofBool)$', head):
        return 'applicative'
    if 'Circuit' in head or head.startswith(
            ('Sparkle.Core.HList', 'Sparkle.Core.Reg', 'Sparkle.Core.RegList')) or head in (
            'List.cons', 'List.nil', 'Unit.unit', 'PUnit.unit'):
        return 'circuit-do'
    if head in ("BitVec.extractLsb'", 'HAppend.hAppend', 'BitVec.append'):
        return 'slice/concat'
    if 'memoryComboRead' in head:
        return 'comboRead'
    if head.startswith(('Sparkle.Core.', 'BitVec.')) or head.split('.')[0] in (
            'Nat', 'Bool', 'Fin', 'ite', 'dite', 'List', 'Array', 'id', 'cond', 'Decidable',
            'Eq', 'HEq'):
        return 'other:' + head
    return 'userdef/struct'


def sets():
    """Blocker SETS per declaration: a declaration is unlocked only when every
    feature in its set is certified.  argv[3] names the reasons file."""
    name = sys.argv[3] if len(sys.argv) > 3 else 'cov_reasons.txt'
    seen = {}
    for line in open(f'{work}/{name}'):
        p = line.rstrip('\n').split('\t')
        if len(p) == 3:
            seen.setdefault(p[0], (p[1], p[2]))
    blockers = {}
    for decl, (sc, r) in seen.items():
        s = set()
        if sc == 'nonscalar':
            s.add('nonscalar-result')
        if r.startswith('BINDER:'):
            s.add('binder')
        else:
            body = r[5:]
            if body.endswith(' +instances'):
                body = body[:-len(' +instances')]
                s.add('instances')
            if body == '(vocabulary only)':
                s.add('shape')
            else:
                # A concrete clock domain is not a blocker by itself (cones and
                # instance spines at `defaultDomain` are accepted).
                s.update(feature(h) for h in body.split(',')
                         if h != 'Sparkle.Core.Domain.defaultDomain')
        blockers[decl] = frozenset(s)
    count = collections.Counter(blockers.values())
    print('declarations:', len(blockers), 'distinct blocker sets:', len(count))
    for k, v in count.most_common(15):
        print(f'  {v:4d}  {sorted(k)}')
    feats = sorted({f for s in blockers.values() for f in s})
    print('declarations containing each feature / blocked by it alone:')
    for f in sorted(feats, key=lambda f: -sum(1 for s in blockers.values() if f in s)):
        if f.startswith('other:'):
            continue
        print(f'  {sum(1 for s in blockers.values() if f in s):4d} / '
              f'{sum(1 for s in blockers.values() if s == frozenset([f])):3d}  {f}')
    chosen = set()
    print('greedy unlock order (cumulative declarations unlocked):')
    for _ in range(len(feats)):
        best = None
        for f in feats:
            if f in chosen:
                continue
            key = (sum(1 for s in blockers.values() if s <= chosen | {f}),
                   sum(1 for s in blockers.values() if f in s))
            if best is None or key > best[0]:
                best = (key, f)
        chosen.add(best[1])
        print(f'  + {best[1]:18s} -> {best[0][0]}')
        if best[0][0] == len(blockers):
            break


{'routes': routes, 'reasons': reasons, 'sets': sets}[mode]()
