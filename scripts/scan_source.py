#!/usr/bin/env python3
"""Textual audit aid: list proof holes, bypass hooks and native calls in authored Lean sources."""
import json
from pathlib import Path
import re
import sys

repo = Path(__file__).resolve().parents[1]
patterns = {
    'proof_holes': r'\b(sorry|admit)\b',
    'authored_axiom': r'^\s*(?:(?:private|protected)\s+)?axiom\b',
    'bypass_hooks': r'\b(unsafe|implemented_by|extern|opaque|partial|elab_rules|modifyEnv|addDecl|skipKernel|trustLevel)\b',
    'external_execution_or_data': r'\b(IO|run_tac|include_str|readFile)\b|#eval\b',
    'native_calls': r'\bnative_decide\b',
}
result = {'scope': 'authored lean/**/*.lean, excluding .lake', 'files': 0, 'matches': {k: [] for k in patterns}}
# Comments are retained: reported matches must be read, not automatically called vulnerabilities.
for p in sorted((repo / 'lean').rglob('*.lean')):
    if '.lake' in p.parts:
        continue
    result['files'] += 1
    for n, line in enumerate(p.read_text().splitlines(), 1):
        for name, pattern in patterns.items():
            if re.search(pattern, line):
                result['matches'][name].append({'path': str(p.relative_to(repo)), 'line': n, 'text': line.strip()})
print(json.dumps(result, indent=2))
# A scan is an aid to inspection, not a semantic proof or a substitute for #print axioms.
