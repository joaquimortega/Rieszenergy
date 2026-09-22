#!/usr/bin/env python3
"""Check structural coverage, not mathematical proof completion."""
import re
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
modules = {p.stem: p for p in (ROOT / 'BEMOCFormalization').glob('*.lean')}
imports = re.compile(r'^import BEMOCFormalization\.([A-Za-z0-9_]+)$', re.M)
errors = []
visited = set()
def visit(name):
    if name in visited:
        return
    visited.add(name)
    if name not in modules:
        errors.append(f'missing imported module {name}')
        return
    for child in imports.findall(modules[name].read_text()):
        visit(child)
for name in imports.findall((ROOT / 'BEMOCFormalization.lean').read_text()):
    visit(name)
for name, path in modules.items():
    if name not in visited:
        errors.append(f'module not imported by root: {name}')
    guide = ROOT / 'blueprint/modules' / (name + '.md')
    if not guide.exists():
        errors.append(f'missing proof guide: {name}')
    text = path.read_text()
    if re.search(r'^\s*(?:axiom|opaque)\b|\b(?:sorry|admit)\b', text, re.M):
        errors.append(f'forbidden proof shortcut or ambiguous mention: {name}')
root_text = (ROOT / 'BEMOCFormalization.lean').read_text()
if re.search(r'^\s*(?:axiom|opaque)\b|\b(?:sorry|admit)\b', root_text, re.M):
    errors.append('forbidden shortcut in entry point')
if errors:
    raise SystemExit('\n'.join(errors))
print(f'All {len(modules)} active modules are imported and documented; source shortcut audit passed.')
print('This structural check does not prove any open proposition contract.')
