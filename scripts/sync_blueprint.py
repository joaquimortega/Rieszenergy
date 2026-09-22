#!/usr/bin/env python3
"""Synchronize full Lean module listings in the per-module proof guides."""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
START = '<!-- LEAN_STATEMENTS -->'
END = '<!-- END_LEAN_STATEMENTS -->'
parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true')
args = parser.parse_args()
failures = []
for lean in sorted((ROOT / 'BEMOCFormalization').glob('*.lean')):
    guide = ROOT / 'blueprint/modules' / (lean.stem + '.md')
    if not guide.exists():
        failures.append(f'missing guide: {guide.relative_to(ROOT)}')
        continue
    original = guide.read_text()
    if START not in original:
        failures.append(f'missing marker: {guide.relative_to(ROOT)}')
        continue
    before, after = original.split(START, 1)
    if END in after:
        after = after.split(END, 1)[1]
    listing = START + '\n\n## Exact checked Lean source\n\n```lean\n' + lean.read_text().rstrip() + '\n```\n\n' + END
    expected = before + listing + after
    if args.check:
        if expected != original:
            failures.append(f'stale listing: {guide.relative_to(ROOT)}')
    else:
        guide.write_text(expected)
if failures:
    raise SystemExit('\n'.join(failures))
print('Blueprint Lean listings are ' + ('current.' if args.check else 'synchronized.'))
