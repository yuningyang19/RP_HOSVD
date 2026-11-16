#!/usr/bin/env python3
"""Check inventory completeness, exact public signatures, and each transitive axiom set.
Run after lake build. The direct Lean check is also available in Audit.lean.
"""
import argparse
import json
import re
from pathlib import Path
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--write-audit', action='store_true',
                    help='regenerate the checked-in Lean audit file and stop')
args = parser.parse_args()
records = json.loads((root/'inventory.json').read_text())['results']
targets = json.loads((root/'targets.json').read_text())
if [r['label'] for r in records] != list(targets):
    sys.exit('Numbered manuscript labels and target mapping differ.')
if len(set(v[1] for v in targets.values())) != len(records):
    sys.exit('Duplicate proof binding.')
parts = ['import RPHOSVD\n']
for label, (claim, proof, module) in targets.items():
    if not (root/module).is_file():
        sys.exit(f'Missing source for {label}: {module}')
    parts.append(f'-- {label}\nexample : {claim} := {proof}\n#print axioms {proof}\n')
src = '\n'.join(parts)
audit = root/'Audit.lean'
if args.write_audit:
    audit.write_text(src)
    sys.exit(0)
if src != audit.read_text():
    sys.exit('Audit.lean and target bindings differ.')
check = subprocess.run(['lake','env','lean','Audit.lean'],cwd=root,
                       stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True)
print(check.stdout, end='')
if check.returncode:
    sys.exit(check.returncode)
allowed = {'propext','Classical.choice','Quot.sound'}
for _, proof, _ in targets.values():
    match = re.search(r"'"+re.escape(proof)+r"' depends on axioms:\s*\[([^\]]*)\]",check.stdout)
    if match:
        axs = {a.strip() for a in match[1].split(',') if a.strip()}
        if axs <= allowed:
            continue
    if "'"+proof+"' does not depend on any axioms" not in check.stdout:
        sys.exit(f'Missing evidence or unexpected axiom for {proof}')
print(f'{len(records)} distinct theorem signatures and transitive axiom lists checked.')
