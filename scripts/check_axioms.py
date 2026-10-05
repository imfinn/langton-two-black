#!/usr/bin/env python3
"""Check the expected axiom grouping in freshly printed theoremA output."""
import json
from pathlib import Path
import re
import sys

path = Path(sys.argv[1])
match = re.search(r"'TwoBlack\.theoremA' depends on axioms:\s*\[(.*?)\]", path.read_text(), re.S)
if not match:
    raise SystemExit('Missing theoremA axiom report')
axioms = [x.strip() for x in match.group(1).split(',') if x.strip()]
standard = {'propext', 'Quot.sound', 'Classical.choice'}
other = [x for x in axioms if x not in standard]
if set(axioms) & standard != standard or len(axioms) != 64 or len(set(axioms)) != 64:
    raise SystemExit('Unexpected final axiom count or standard-axiom set')
if len(other) != 61 or any('native_decide.ax' not in x for x in other):
    raise SystemExit('Unexpected nonstandard axiom: review the report')
result = {'theorem': 'TwoBlack.theoremA', 'standard': sorted(standard), 'native_count': len(other), 'axioms': axioms}
path.with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
print('theoremA: 3 standard axioms + 61 native computation axioms; no other axioms')
