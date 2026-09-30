import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {test} from 'node:test';
import {fileURLToPath} from 'node:url';
import {CheckLeanAxiomTranscript0} from '../scripts/check-lean-axioms.mjs';
import {ComputeLeanSourceClosureSha2560} from '../formal-publication0.mjs';

const ROOT = fileURLToPath(new URL('..', import.meta.url));
const STAGES = [
  {
    "source": "lean/PNP/NANDJointAsymmetricBound.lean",
    "names": [
      "PNP.DirectWire.JointAsymmetricBound.zero_budget_read_once",
      "PNP.DirectWire.JointAsymmetricBound.asymmetric_bound",
      "PNP.DirectWire.JointAsymmetricBound.two_positions_permutation",
      "PNP.DirectWire.JointAsymmetricBound.two_output_positions_bound"
    ],
    "auditFile": "lean-audit/PNPJointAsymmetricBoundAxiomAudit.lean"
  },
  {
    "source": "lean/PNP/NANDGuardedSpineSupportMinimum.lean",
    "names": [
      "PNP.DirectWire.GuardedSpineSupportMinimum.first_only_minimum",
      "PNP.DirectWire.GuardedSpineSupportMinimum.both_ends_minimum",
      "PNP.DirectWire.GuardedSpineSupportMinimum.proper_minimum"
    ],
    "auditFile": "lean-audit/PNPGuardedSpineSupportMinimumAxiomAudit.lean"
  },
  {
    "source": "lean/PNP/NANDGuardedSpineBoundedQuiet.lean",
    "names": [
      "PNP.DirectWire.GuardedSpineBoundedQuiet.proper_of_small_support",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.bounded_quiet",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.scan_none",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.quiet_with_strict_gain",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.quiet_nonminimum_exists",
      "PNP.DirectWire.GuardedSpineBoundedQuiet.no_uniform_zero_slack_limit"
    ],
    "auditFile": "lean-audit/PNPGuardedSpineBoundedQuietAxiomAudit.lean"
  }
];
const read0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
const names = STAGES.flatMap(stage => stage.names);
const allowed = new Set(['Quot.sound', 'propext']);

test('fixed-window obstruction publication binds every conclusion to the compiled explicit root', async () => {
  const inventory = JSON.parse(await read0('status/LEAN_THEOREM_INVENTORY.json'));
  assert.equal(await read0('public/pnp-theorem-inventory.json'), await read0('status/LEAN_THEOREM_INVENTORY.json'));
  for (const stage of STAGES) {
    for (const name of stage.names) {
      const entries = inventory.declarations.filter(row => row.name === name);
      assert.equal(entries.length, 1, name);
      assert.equal(entries[0].kind, 'theorem', name);
      assert.equal(entries[0].module, stage.source.replace('lean/', '').replaceAll('/', '.').replace('.lean', ''), name);
      assert.ok(entries[0].axioms.every(axiom => allowed.has(axiom)), name);
    }
    const audit = await read0(stage.auditFile);
    const transcript = stage.names.map(name => {
      const axioms = inventory.declarations.find(row => row.name === name).axioms;
      return "'" + name + "'" + (axioms.length ? ' depends on axioms: [' + axioms.join(', ') + ']' : ' does not depend on any axioms');
    }).join('\n') + '\n';
    assert.deepEqual(CheckLeanAxiomTranscript0(transcript, audit, inventory.declarations).sort(), stage.names.slice().sort());
    const missing = inventory.declarations.filter(row => row.name !== stage.names[0]);
    assert.throws(() => CheckLeanAxiomTranscript0(transcript, audit, missing), /missing or duplicate/u);
    const changed = inventory.declarations.map(row => row.name === stage.names[0] ? {...row, axioms: [...row.axioms, 'Classical.choice'].sort()} : row);
    assert.throws(() => CheckLeanAxiomTranscript0(transcript, audit, changed));
  }
  const map = JSON.parse(await read0('publication/FORMAL_PUBLICATION_MAP.json'));
  assert.equal(map.milestoneSourceClosureSha256, await ComputeLeanSourceClosureSha2560(ROOT, inventory));
  assert.equal(map.milestones.some(row => row.requiredTheorems.some(name => names.includes(name))), false,
    'a route limitation must not silently become an earned positive roadmap row');
});
