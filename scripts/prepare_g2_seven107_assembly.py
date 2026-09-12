"""Regenerate the grouped modulus-107 reduction from authored certificate data.

Reads witness trees, authored Python generator functions, and audited compiler
types. Does not discover or edit declarations in Lean source text.
"""
from pathlib import Path
import argparse, ast, hashlib, json

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--bundle', type=Path, required=True)
p.add_argument('--groups', type=Path, required=True)
p.add_argument('--output', type=Path, required=True)
p.add_argument('--mode', choices=['direct', 'destructure', 'imports', 'nodes'], default='nodes')
opts = p.parse_args()
base, groups, out = opts.bundle.resolve(), opts.groups.resolve(), opts.output.resolve()
assert not out.exists()
plan = json.loads((base / 'plan.json').read_text())
group_plan = json.loads((groups / 'preparation.json').read_text())
assert json.loads((base / 'verification.json').read_text())['both_revisions_pass']
types = {label: {r['name']: r['type'] for r in map(json.loads, (base / label / 'types.jsonl').read_text().splitlines())}
         for label in ['original', 'supported']}

generator = base / 'generate_source.py'
tree = ast.parse(generator.read_text())
functions = ast.Module(body=[n for n in tree.body if isinstance(n, ast.FunctionDef)], type_ignores=[])
env = {'budget': plan['budget_leaves_per_certificate_theorem'], 'sizes': {},
       'terminals': [], 'assemblies': [], 'inlines': {}}
exec(compile(functions, str(generator), 'exec'), env)
keep, row_roots = [], {}
for label, prefix, start in [('Unit', [0, 1], 2), ('Nonunit', [0], 1)]:
    t = json.loads((base / 'experiments' / f'{label.lower()}-107.json').read_text())
    keep.append(t)
    row_roots[label] = [(a, env['walk'](label, prefix + [a], a, child)) for a, child in enumerate(t, start)]
assert len(env['terminals']) == plan['terminal_certificates']
assert len(env['assemblies']) == plan['assembly_nodes']

namespace = 'MinModulus.PrefixCertificate.G2Seven107'
projection, group_locals, aliases = {}, [], []
for group, r in enumerate(group_plan['records']):
    count = len(r['component_theorems'])
    locals_for_group = []
    for i, name in enumerate(r['component_theorems']):
        assert types['original'][name] == types['supported'][name]
        local = f't{group}_{i}'
        locals_for_group.append(local)
        base_term = r['target'] if opts.mode in ['imports', 'nodes'] else 'h' + str(group)
        short_name = name.removeprefix(namespace + '.').removesuffix('_closed')
        expression = base_term + '.2' * i + ('.1' if i < count - 1 else '')
        projection[short_name] = (
            base_term + '.2' * i + ('.1' if i < count - 1 else '')
            if opts.mode in ['direct', 'imports'] else local)
        if opts.mode == 'nodes':
            projection[short_name] = short_name + '_closed'
            aliases.append({'local_name': short_name + '_closed', 'component': name,
                            'type': types['supported'][name], 'proof': expression})
    group_locals.append(locals_for_group)
assert set(projection) == {r['name'] for r in env['terminals']}

def proof(name):
    return projection[name] if name in projection else env['proof_of'](name)

text = '''import MinModulus.PrefixCertificateMinimalAssembly

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

open MinModulus.PrefixCertificate

/-- The eleven grouped certificate statements imply the unconditional modulus-107 exclusion.
Each group has an independent, separately checked proof. -/
theorem MinModulus.Research.seven107_of_grouped_certificates
'''
if opts.mode in ['imports', 'nodes']:
    text = ''.join('import ' + Path(r['target_file']).stem + '\n' for r in group_plan['records']) + '''
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

open MinModulus.PrefixCertificate

/-- Assemble the eleven proved certificate conjunctions into the modulus-107 exclusion. -/
theorem MinModulus.Research.not_validTuple_seven_mod_107_grouped
'''
else:
    for group, r in enumerate(group_plan['records']):
        statement = ' ∧\n'.join('(' + types['supported'][name] + ')' for name in r['component_theorems'])
        text += '    (h' + str(group) + ' :\n' + statement + ')\n'
if opts.mode == 'nodes':
    text = ''.join('import ' + Path(r['target_file']).stem + '\n' for r in group_plan['records']) + '''
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

open MinModulus.PrefixCertificate
namespace MinModulus.Research.G2Seven107Assembled

'''
    for alias in aliases:
        text += 'theorem ' + alias['local_name'] + ' : ' + alias['type'] + ' :=\n  ' + alias['proof'] + '\n\n'
else:
    text += '    (g : Fin 7 → ZMod 107) : ¬ MinModulus.ValidTuple g := by\n'
if opts.mode == 'destructure':
    for group, names in enumerate(group_locals):
        pattern = '⟨' + ', '.join(names) + '⟩' if len(names) > 1 else names[0]
        text += '  rcases h' + str(group) + ' with ' + pattern + '\n'
for r in env['assemblies']:
    declaration = 'theorem ' if opts.mode == 'nodes' else '  have '
    indent = '  ' if opts.mode == 'nodes' else '    '
    text += declaration + r['name'] + '_closed : ClosedMinimalPrefix ' + env['args'](r) + ' := by\n'
    text += indent + 'apply closedMinimalPrefix_of_children\n' + indent + 'intro x hlo hhi\n' + indent + 'interval_cases x\n'
    text += ''.join(indent + '· exact ' + proof(name) + '\n' for name in r['children'])
for label, start, mode, k, prefix in [('Unit', 2, 'true', 4, '[0,1,a]'), ('Nonunit', 1, 'false', 5, '[0,a]')]:
    declaration = 'theorem ' if opts.mode == 'nodes' else '  have '
    indent = '  ' if opts.mode == 'nodes' else '    '
    text += declaration + label.lower() + '_closed (a : ℕ) (hlo : ' + str(start) + ' ≤ a) (hhi : a < 107) :\n'
    text += indent + '  ClosedMinimalPrefix ' + mode + ' 107 a ' + str(k) + ' ' + prefix + ' (a+1) := by\n' + indent + 'interval_cases a\n'
    text += ''.join(indent + '· exact ' + proof(name) + '\n' for _, name in row_roots[label])
if opts.mode == 'nodes':
    text += '''
end MinModulus.Research.G2Seven107Assembled

open MinModulus.Research.G2Seven107Assembled in
/-- Assemble the eleven proved certificate conjunctions into the modulus-107 exclusion. -/
theorem MinModulus.Research.not_validTuple_seven_mod_107_grouped
    (g : Fin 7 → ZMod 107) : ¬ MinModulus.ValidTuple g := by
'''
text += '''  letI : Nontrivial (ZMod 107) := ⟨⟨0, 1, by decide⟩⟩
  exact not_validTuple_of_minimal_prefixes (by decide) unit_closed nonunit_closed g

'''
target = ('MinModulus.Research.not_validTuple_seven_mod_107_grouped' if opts.mode in ['imports', 'nodes']
          else 'MinModulus.Research.seven107_of_grouped_certificates')
text += '#print axioms ' + target + '\n'
out.mkdir(parents=True)
source = out / 'Seven107GroupedAssembly.lean'
source.write_text(text)
copied_group_sources = {}
if opts.mode in ['imports', 'nodes']:
    for r in group_plan['records']:
        group_source = groups / r['target_file']
        digest = hashlib.sha256(group_source.read_bytes()).hexdigest()
        assert digest == r['target_sha256']
        (out / group_source.name).write_bytes(group_source.read_bytes())
        copied_group_sources[group_source.name] = digest
metadata = {'mode': opts.mode, 'target': target, 'generated_source': source.name,
            'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
            'authored_generator_sha256': hashlib.sha256(generator.read_bytes()).hexdigest(),
            'group_parameters': 0 if opts.mode in ['imports', 'nodes'] else len(group_plan['records']),
            'imported_group_theorems': [r['target'] for r in group_plan['records']] if opts.mode in ['imports', 'nodes'] else [],
            'terminal_components': len(projection),
            'copied_group_source_sha256': copied_group_sources,
            'local_assembly_nodes': len(env['assemblies']), 'source_bytes': source.stat().st_size,
            'assembly_helper_names': ['MinModulus.Research.G2Seven107Assembled.' + r['name'] + '_closed' for r in env['assemblies']] if opts.mode == 'nodes' else [],
            'projection_aliases': aliases,
            'lean_checked': False, 'scope': ('Unconditional exclusion assembled from eleven proved group imports.' if opts.mode in ['imports', 'nodes'] else 'Reduction from eleven explicit certificate conjunctions.')}
(out / 'preparation.json').write_text(json.dumps(metadata, indent=2) + '\n')
print(json.dumps({k: v for k, v in metadata.items() if k not in ['projection_aliases', 'assembly_helper_names']}, indent=2))
