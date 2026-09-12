"""Prepare grouped certificate statements and independent inline-data proofs.

Uses authored certificate metadata, audited Lean types, and the original JSON
witness trees. No Lean declarations are extracted from source text. Generated files must be checked against both Lean revisions before upload.
The archived eleven-group instance has passed those checks.
"""
from pathlib import Path
import argparse
import hashlib
import json

MODULUS = 107
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--bundle', type=Path, required=True, help='Verified g2-seven-odd-107 evidence archive')
parser.add_argument('--output', type=Path, required=True, help='New output directory')
options = parser.parse_args()
BASE = options.bundle.resolve()
TREES = BASE / 'experiments'
OUT = options.output.resolve()
assert not OUT.exists(), 'Inspect the existing probes rather than overwriting them.'
plan = json.loads((BASE / 'plan.json').read_text())
verification = json.loads((BASE / 'verification.json').read_text())
assert verification['both_revisions_pass']
types = {}
for label in ['original', 'supported']:
    types[label] = {row['name']: row for row in map(
        json.loads, (BASE / label / 'types.jsonl').read_text().splitlines())}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def weight(tree):
    return sum(map(weight, tree)) if isinstance(tree, list) else 1


def render(tree):
    if isinstance(tree, int):
        return '.stop (.collision ' + str(tree) + ')'
    if isinstance(tree, dict):
        assert len(tree) == 1
        kind, values = next(iter(tree.items()))
        assert kind in ['unit', 'pair', 'third']
        return '.stop (.' + ('unitPair' if kind == 'unit' else kind) + ' ' + ' '.join(map(str, values)) + ')'
    assert isinstance(tree, list)
    return '.branch [' + ','.join(map(render, tree)) + ']'


terminals = {}


def visit(label, prefix, anchor, tree):
    size = weight(tree)
    if size <= 64:
        return
    if size <= plan['budget_leaves_per_certificate_theorem']:
        local = label.lower() + '_' + '_'.join(map(str, prefix[2:] if label == 'Unit' else prefix[1:]))
        name = 'MinModulus.PrefixCertificate.G2Seven107.' + local + '_closed'
        assert name not in terminals
        terminals[name] = {'label': label, 'prefix': prefix, 'anchor': anchor,
                           'tree': tree, 'weight': size}
        return
    assert isinstance(tree, list) and len(tree) == MODULUS - prefix[-1] - 1
    for next_value, child in enumerate(tree, prefix[-1] + 1):
        visit(label, prefix + [next_value], anchor, child)


for label, prefix, first in [('Unit', [0, 1], 2), ('Nonunit', [0], 1)]:
    tree = json.loads((TREES / (label.lower() + '-107.json')).read_text())
    assert len(tree) == MODULUS - first
    for anchor, child in enumerate(tree, first):
        visit(label, prefix + [anchor], anchor, child)

certificate_modules = [row for row in plan['modules'] if row['kind'] == 'certificate']
planned_names = [name for row in certificate_modules for name in row['checked_theorems']]
assert set(planned_names) == terminals.keys()
assert len(planned_names) == len(set(planned_names)) == plan['terminal_certificates']
OUT.mkdir()
records = []
for row in certificate_modules:
    names = row['checked_theorems']
    assert sum(terminals[name]['weight'] for name in names) == row['weight']
    for name in names:
        assert types['original'][name]['type'] == types['supported'][name]['type']
    source = BASE / (row['module'].replace('.', '/') + '.lean')
    assert sha(source) == plan['source_hashes'][str(source.relative_to(BASE))]
    slug = row['module'].rsplit('.', 1)[1]
    target_name = 'MinModulus.PrefixCertificate.G2Seven107.' + slug[0].lower() + slug[1:] + '_closed'
    statement = ' ∧\n'.join('(' + types['supported'][name]['type'] + ')' for name in names)
    header = 'set_option autoImplicit false\nset_option maxRecDepth 2000000\nset_option maxHeartbeats 0\n\n'
    target = 'import ' + row['module'] + '\n\n' + header
    target += 'theorem ' + target_name + ' :\n' + statement + ' := by\n  exact '
    target += (names[0] if len(names) == 1 else '⟨' + ', '.join(names) + '⟩') + '\n'
    target += '\n#print axioms ' + target_name + '\n'
    proof = 'import MinModulus.PrefixCertificateMinimalAssembly\n\n' + header
    proof += 'open MinModulus.PrefixCertificate\n\ntheorem solution :\n' + statement + ' := by\n'
    if len(names) > 1:
        proof += '  refine ⟨' + ', '.join('?_' for _ in names) + '⟩\n'
    for name in names:
        item = terminals[name]
        prefix = item['prefix']
        arguments = ('true' if item['label'] == 'Unit' else 'false') + ' 107 '
        arguments += str(item['anchor']) + ' ' + str(7 - len(prefix)) + ' '
        arguments += str(prefix).replace(' ', '') + ' ' + str(prefix[-1] + 1)
        indent = '    ' if len(names) > 1 else '  '
        proof += ('  · ' if len(names) > 1 else '  ') + 'let cert : MinimalCertificate :=\n'
        proof += indent + '  ' + render(item['tree']) + '\n'
        proof += indent + 'exact closedMinimalPrefix_of_verify ' + arguments + ' cert (by decide +kernel)\n'
    proof += '\n#print axioms solution\n'
    target_path = OUT / (slug + 'Target.lean')
    proof_path = OUT / (slug + 'Proof.lean')
    target_path.write_text(target)
    proof_path.write_text(proof)
    records.append({'module': row['module'], 'target': target_name,
                    'component_theorems': names, 'terminal_witnesses': row['weight'],
                    'source_module_sha256': sha(source),
                    'target_file': target_path.name, 'target_sha256': sha(target_path),
                    'proof_file': proof_path.name, 'proof_sha256': sha(proof_path),
                    'proof_bytes': proof_path.stat().st_size})

(OUT / 'preparation.json').write_text(json.dumps({
    'lean_checked': False, 'publication_ready': False,
    'purpose': 'Probe grouped statements with certificate data local to their solutions.',
    'modulus': 107, 'grouped_statement_count': len(records),
    'component_theorem_count': len(planned_names),
    'source': str(BASE), 'records': records}, indent=2) + '\n')
print('Prepared', len(records), 'grouped statements covering', len(planned_names),
      'individually audited certificate theorems. Lean checks remain pending.')
