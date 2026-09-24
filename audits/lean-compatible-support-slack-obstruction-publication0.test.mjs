import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {CheckLeanAxiomTranscript0} from '../scripts/check-lean-axioms.mjs';
import {ComputeLeanSourceClosureSha2560} from '../formal-publication0.mjs';
import {fileURLToPath} from 'node:url';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const read0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const namespace = 'PNP.DirectWire.CompatibleSupportSlackObstruction.';
const names = [
  'formula_exact', 'baseline', 'no_output_is_first_nand', 'gate_lower_bound',
  'original_is_minimum', 'original_reference_minimum', 'global_slack_zero',
  'boundary_exact', 'interface_exact', 'selected_gate_count',
  'smaller_formula_exact', 'same_open_function', 'comparison_reference_minimum',
  'literal_splice_is_cyclic', 'open_baseline', 'local_reference_minimum',
  'local_slack_one', 'global_slack_law_violation',
].map(name => namespace + name).sort();

test('slack obstruction publication retains exact compiled theorem closures without a new earned row', async () => {
  const inventory = JSON.parse(await read0('status/LEAN_THEOREM_INVENTORY.json'));
  assert.equal(await read0('public/pnp-theorem-inventory.json'), await read0('status/LEAN_THEOREM_INVENTORY.json'));
  for (const name of names) {
    const entries = inventory.declarations.filter(row => row.name === name);
    assert.equal(entries.length, 1, name);
    assert.equal(entries[0].kind, 'theorem', name);
    assert.deepEqual(entries[0].axioms, ['Quot.sound', 'propext'], name);
  }
  const audit = await read0('lean-audit/PNPCompatibleSupportSlackObstructionAxiomAudit.lean');
  const transcript = names.map(name => "'" + name + "' depends on axioms: [propext, Quot.sound]").join('\n') + '\n';
  assert.deepEqual(CheckLeanAxiomTranscript0(transcript, audit, inventory.declarations).sort(), names);
  const missing = inventory.declarations.filter(row => row.name !== names[0]);
  assert.throws(() => CheckLeanAxiomTranscript0(transcript, audit, missing), /missing or duplicate/u);
  const map = JSON.parse(await read0('publication/FORMAL_PUBLICATION_MAP.json'));
  assert.equal(map.milestoneSourceClosureSha256, await ComputeLeanSourceClosureSha2560(ROOT, inventory));
  assert.equal(map.milestones.some(row => row.requiredTheorems.some(name => names.includes(name))), false,
    'a negative finding must not silently become an earned positive roadmap row');
});
