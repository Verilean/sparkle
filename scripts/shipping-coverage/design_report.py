#!/usr/bin/env python3
"""Report of scripts/shipping-coverage/design_sweep.sh (round par/b-36).

    design_report.py WORKDIR

Reads WORKDIR/files_given.txt, WORKDIR/done/*.status and WORKDIR/rows/*.txt.
Every line it prints says "N of the M files given": a subset is never
reported as the corpus.  WRITTEN, NOT RUN.
"""
import collections
import os
import sys


def main():
    work = sys.argv[1]
    given = [l.strip() for l in open(os.path.join(work, 'files_given.txt')) if l.strip()]
    m = len(given)
    status = {}
    for f in given:
        key = f.replace('/', '_')
        p = os.path.join(work, 'done', key + '.status')
        if os.path.exists(p):
            # "file=… result=… exit=… seconds=… peak=…" (a path has no space here)
            status[f] = dict(kv.split('=', 1) for kv in open(p).read().split() if '=' in kv)
    done = [f for f in given if f in status]
    measured = [f for f in done if status[f].get('result') == 'measured']
    scope = f'{len(measured)} of the {m} files given'
    print(f'files with a status: {len(done)} of the {m} files given; '
          f'measured (reached FILE-DONE): {scope}')
    for f in done:
        d = status[f]
        if d.get('result') != 'measured':
            print(f"  UNMEASURED {f}: {d.get('result')} (exit {d.get('exit')}, "
                  f"{d.get('seconds')} s, peak {d.get('peak')})")
    for f in given:
        if f not in status:
            print(f'  NOT RUN {f}')
    rows = []
    for f in done:
        p = os.path.join(work, 'rows', f.replace('/', '_') + '.txt')
        if not os.path.exists(p):
            continue
        for line in open(p):
            parts = line.rstrip('\n').split('|', 7)
            if len(parts) == 8 and parts[3] != 'FILE-DONE':
                rows.append(parts)
    # candidates are the definitions declared in the file itself, so a
    # declaration has a row in ONE file of the list
    by = collections.Counter((r[3], r[4]) for r in rows)
    print(f'candidates with a row: {len(rows)} ({scope}; rows of unmeasured files are '
          f'included, their missing candidates are UNMEASURED, not failed)')
    for (cls, outcome), n in sorted(by.items()):
        print(f'  {cls:12s} {outcome:14s} {n}   [{scope}]')
    forms = collections.Counter(r[5] for r in rows if r[4] == 'COVERED')
    for form, n in sorted(forms.items()):
        print(f'  COVERED by {form}: {n}   [{scope}]')

    def ms(r):
        return int(r[6]) if r[6].isdigit() else 0

    print(f'slowest candidates (ms) [{scope}]:')
    for r in sorted(rows, key=ms, reverse=True)[:10]:
        print(f'  {r[6]:>8s}  {r[1]}  {r[3]} {r[4]}  ({r[0]})')
    for r in rows:
        if r[4] in ('NOT-COVERED', 'ERROR'):
            print(f'  {r[4]} {r[1]} [{r[3]}] ({r[0]}): {r[7][:300]}')
    secs = [int(status[f]['seconds']) for f in done if status[f].get('seconds', '').isdigit()]
    if secs:
        print(f'wall time per file: total {sum(secs)} s, max {max(secs)} s   '
              f'[{len(done)} of the {m} files given]')


if __name__ == '__main__':
    main()
