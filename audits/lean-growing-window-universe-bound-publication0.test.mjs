import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {fileURLToPath} from 'node:url';
import {CheckLeanAxiomTranscript0} from '../scripts/check-lean-axioms.mjs';
import {ComputeLeanSourceClosureSha2560} from '../formal-publication0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const NAMESPACE = 'PNP.DirectWire.GrowingWindowUniverseBound';
const NAMES = [
  'programs_tail_length_le', 'smallerCandidates_exceeds_polynomial',
  'query_length_le', 'valid_requires_full_budget',
  'valid_universe_exceeds_encoded_polynomial', 'no_uniform_polynomial_complete_universe',
].map(name => NAMESPACE + '.' + name);
const read0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const allowed = new Set(['Quot.sound', 'propext']);

test('growing-window boundary is compiled, source-bound and not an earned positive milestone', async () => {
  const bytes = await read0('status/LEAN_THEOREM_INVENTORY.json');
  assert.equal(await read0('public/pnp-theorem-inventory.json'), bytes);
  const inventory = JSON.parse(bytes);
  for (const name of NAMES) {
    const matching = inventory.declarations.filter(row => row.name === name);
    assert.equal(matching.length, 1, name);
    assert.equal(matching[0].kind, 'theorem', name);
    assert.equal(matching[0].module, 'PNP.NANDGrowingWindowUniverseBound', name);
    assert.ok(matching[0].axioms.every(axiom => allowed.has(axiom)), name);
  }
  const audit = await read0('lean-audit/PNPGrowingWindowUniverseBoundAxiomAudit.lean');
  const transcript = NAMES.map(name => {
    const axioms = inventory.declarations.find(row => row.name === name).axioms;
    return "'" + name + "'" + (axioms.length ? ' depends on axioms: [' + axioms.join(', ') + ']' : ' does not depend on any axioms');
  }).join('\n') + '\n';
  assert.deepEqual(CheckLeanAxiomTranscript0(transcript, audit, inventory.declarations).sort(), NAMES.slice().sort());
  const missing = inventory.declarations.filter(row => row.name !== NAMES[0]);
  assert.throws(() => CheckLeanAxiomTranscript0(transcript, audit, missing), /missing or duplicate/u);
  const altered = inventory.declarations.map(row => row.name === NAMES[0]
    ? {...row, axioms: [...row.axioms, 'Classical.choice'].sort()} : row);
  assert.throws(() => CheckLeanAxiomTranscript0(transcript, audit, altered));
  const map = JSON.parse(await read0('publication/FORMAL_PUBLICATION_MAP.json'));
  assert.equal(map.milestoneSourceClosureSha256, await ComputeLeanSourceClosureSha2560(ROOT, inventory));
  assert.equal(map.milestones.some(row => row.requiredTheorems.some(name => NAMES.includes(name))), false,
    'an enumeration limitation must not become an earned positive roadmap row');
});
