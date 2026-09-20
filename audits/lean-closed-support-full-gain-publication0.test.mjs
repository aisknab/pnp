import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {fileURLToPath} from 'node:url';
import {test} from 'node:test';
import {CheckFormalReconstructionStatus0} from '../pcc-formal-reconstruction-status0.mjs';
import {validateProofProgress0} from '../pcc-proof-progress0.mjs';
import {
  ComputeLeanSourceClosureSha2560, DeriveFormalPublication0,
  MilestoneTheoremKernelTypeSha2560, stableStringify0,
} from '../formal-publication0.mjs';

// Frozen after the explicit-root build and exact compiled axiom audit.
// Runtime tests may not regenerate these pins from their own observed result.
const REVIEWED = [
  [
    "PNP.DirectWire.ClosedSupportFullGain.ambient_output",
    "ee568f70b67653b08b7e6a446f41c4a7afc669fb8d9f64079e17d002ab07f1b9",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.boundarySource_value",
    "af26c3fb2de1f7a161d1070d037d3695e8f6e159af40f5c1345ee2060b3c95d9",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.complement_gate_value",
    "99ad4452989a8e4bbcb7d257dda6e12acd5b6578148579454b6538e78d1b7383",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.fieldSource_value",
    "508f7a818cf914e93b5103db786c749b9e130d90a4e10f6e4b2e860b18fac54c",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.improvement?_none_iff",
    "5f98a2587f19fc9154dc010f322dd6880f46e2a09f4f9e33d87f7bf9e0f9d267",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.improvement?_sound",
    "045804cce1560f746fb655689b7401cae42ba6ffad0359460eba57d6a7daeb6d",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.improvement?_strictGain",
    "26465ff5e8043e1b8348f741c564d7884bf5ea445c2e4f536dafbad61c241a5a",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.inputBinding_eval",
    "100a65ba4f3e2e05637bf7d309187d39d9053ba58768734bcd9c490ab7bac731",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.interface_index_exists",
    "1130fec13c73b0fbc27ee4fb97afebe8c6c3f876372d9a1b4d1714d92c42e249",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.interface_index_sound",
    "832e7b0043849d0b3081e92856e5e41b05b769c241f1f95764e87d88d007d6ae",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.localFullSlack_le_global",
    "77dbb9280db83b5315c6d398f73631b6dacdc79ce42d857d6ef8dc9b111be4a2",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.offered_available",
    "99765be4b85467b2acf1b8fedd80f3a32872e920ba434c1b53e90c0bfac064f8",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.offered_gateCount",
    "7b9303daa49c71db11745cbd8ff49e35e4d2de20de1468f7d6255f3800cb0d51",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.offered_gateCount_le",
    "4dfcc8b90d10ac3201fd9a039a2032b72a88f870d1077bae8527744d782da679",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.outputSource_value",
    "77978caf94fad2d86adb034eeb4127ab697a626979820544a37dba23e6cf48ca",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.prefixField_value",
    "1d426e2e2a43cf3f41d9512c0d60fc8e9a51fe0a70aeffa41460422b34815752",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.prefixOutput_value",
    "66253f4a759423d4beda0ea2524e815ebf052e75ea63565f528e6be1a22c2749",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.prefixSource_value",
    "ab53152242651971b218aafc87ad3538303263b7d4071f89765480452874632e",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.restrict_extendZero",
    "a5894a9fea644ddaf89e902ee96209795e92b627ca1b49834b9e1241d37a6076",
    "PNP.NANDClosedSupportFullGainPrefix",
    [
      "Quot.sound"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.result_exact_accounting",
    "45f5d0e572e15769050735209c56e9826a8d0bbbb79dfeeab872478bb8e5f6b0",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.result_fullEquivalent",
    "c4ce482c3195b7eaf840eb6f6e02ed14fa79e93f15aa0e2774fb8354f53ef095",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.result_fullMinimum",
    "6cf8caaca12504a4ab9a09ba24a02e445a996626500f2fab69034ff6b2f0a93d",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.result_fullSlack_balance",
    "8cb443818ba57aec70181da2ebe015424f9426e5f6e719db8310006b50bb2d2d",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.result_gain_balance",
    "35e9be6bf27970a14e331de0c92c3e90a515d0ad55fbc156442cec161630d939",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.result_output",
    "c670cc9864366a7e5fde03c6f61c76ffd01923ca4e3e9efad64bbd4c1f1621cb",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.result_strict_iff",
    "8fb91b09da8cba2f59fe0dd0bf5aabba01532f870f028ce872dff432683f0f7c",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ],
  [
    "PNP.DirectWire.ClosedSupportFullGain.retained_source_value",
    "b4eb6842f1eddc3c45a6f04d54cee302893708e9d293279d745e7f367abc2c84",
    "PNP.NANDClosedSupportFullGain",
    [
      "Quot.sound",
      "propext"
    ]
  ]
];
const MILESTONE = {
  "classification": "formalized-foundation-only",
  "id": "computed-closed-support-full-profile-gain",
  "nonClaim": "The full-profile minimum, source matching and saturation influence tests remain exhaustive finite reference computations. This does not derive a proper positive support, make whole-span replacements locally VerifyDW-eligible, implement the manuscript's complete noncomputational profile grammar, establish global route coverage or unconditional SaturatePositive, BCELReady or ZeroSlack, or prove complete PCCMin polynomial runtime, output-size or certificate bounds. The eligible root theorem remains absent and P = NP is not proved.",
  "requiredTheorems": [
    "PNP.DirectWire.ClosedSupportFullGain.ambient_output",
    "PNP.DirectWire.ClosedSupportFullGain.boundarySource_value",
    "PNP.DirectWire.ClosedSupportFullGain.complement_gate_value",
    "PNP.DirectWire.ClosedSupportFullGain.fieldSource_value",
    "PNP.DirectWire.ClosedSupportFullGain.improvement?_none_iff",
    "PNP.DirectWire.ClosedSupportFullGain.improvement?_sound",
    "PNP.DirectWire.ClosedSupportFullGain.improvement?_strictGain",
    "PNP.DirectWire.ClosedSupportFullGain.inputBinding_eval",
    "PNP.DirectWire.ClosedSupportFullGain.interface_index_exists",
    "PNP.DirectWire.ClosedSupportFullGain.interface_index_sound",
    "PNP.DirectWire.ClosedSupportFullGain.localFullSlack_le_global",
    "PNP.DirectWire.ClosedSupportFullGain.offered_available",
    "PNP.DirectWire.ClosedSupportFullGain.offered_gateCount",
    "PNP.DirectWire.ClosedSupportFullGain.offered_gateCount_le",
    "PNP.DirectWire.ClosedSupportFullGain.outputSource_value",
    "PNP.DirectWire.ClosedSupportFullGain.prefixField_value",
    "PNP.DirectWire.ClosedSupportFullGain.prefixOutput_value",
    "PNP.DirectWire.ClosedSupportFullGain.prefixSource_value",
    "PNP.DirectWire.ClosedSupportFullGain.restrict_extendZero",
    "PNP.DirectWire.ClosedSupportFullGain.result_exact_accounting",
    "PNP.DirectWire.ClosedSupportFullGain.result_fullEquivalent",
    "PNP.DirectWire.ClosedSupportFullGain.result_fullMinimum",
    "PNP.DirectWire.ClosedSupportFullGain.result_fullSlack_balance",
    "PNP.DirectWire.ClosedSupportFullGain.result_gain_balance",
    "PNP.DirectWire.ClosedSupportFullGain.result_output",
    "PNP.DirectWire.ClosedSupportFullGain.result_strict_iff",
    "PNP.DirectWire.ClosedSupportFullGain.retained_source_value"
  ],
  "scope": "For arbitrary finite wire carriers, keep masks and seed record families under the computed computational-wire-profile model, the full-profile reference minimum of the actual closed support is specialized to primary inputs and reconnected to the derived physical complement. The resulting whole carrier preserves every ordered output and computational field for every input, with exact gate and whole-carrier full-slack balance. Positive computed local full slack yields a checked strict equivalent gain; zero local full slack returns no gain. The support, minimum, source bindings and reconnection are computed, not supplied correctness data.",
  "title": "Computed closed-support full-profile physical gain"
};
const canonical0 = value => Buffer.from(stableStringify0(value) + '\n');
const text0 = file => readFile(new URL('../' + file, import.meta.url), 'utf8');
let loaded;
function sources0() {
  loaded ??= Promise.all([
    text0('status/LEAN_THEOREM_INVENTORY.json'),
    text0('publication/FORMAL_PUBLICATION_MAP.json'),
  ]).then(async ([inventoryText, mapText]) => {
    const inventory = JSON.parse(inventoryText), map = JSON.parse(mapText);
    const sourceClosure = await ComputeLeanSourceClosureSha2560(
      fileURLToPath(new URL('..', import.meta.url)), inventory);
    return {inventory, map, inventoryBytes: Buffer.from(inventoryText), sourceClosure};
  });
  return loaded;
}

test('M278 compiled interface: exact types, modules and axiom closures earn only the reviewed row', async () => {
  const {inventory, map, inventoryBytes, sourceClosure} = await sources0();
  assert.ok(canonical0(inventory).equals(inventoryBytes));
  const names = REVIEWED.map(row => row[0]);
  assert.equal(names.length, 27);
  assert.equal(new Set(names).size, names.length);
  assert.deepEqual(names, MILESTONE.requiredTheorems);
  assert.deepEqual(map.milestones.find(row => row.id === MILESTONE.id), MILESTONE);
  assert.equal(sourceClosure, map.milestoneSourceClosureSha256);
  const publication = DeriveFormalPublication0(inventory, map, inventoryBytes, sourceClosure);
  const row = publication.milestones.find(item => item.id === MILESTONE.id);
  assert.equal(row?.earned, true);
  assert.equal(row.classification, 'formalized-foundation-only');
  assert.equal(publication.gate.passed, false);
  for (const [name, hash, module, axioms] of REVIEWED) {
    for (const collection of [inventory.declarations, inventory.milestoneCandidates]) {
      const found = collection.filter(item => item.name === name);
      assert.equal(found.length, 1, name);
      assert.equal(found[0].kind, 'theorem', name);
      assert.equal(found[0].module, module, name);
      assert.deepEqual(found[0].axioms, axioms, name);
    }
    assert.ok(axioms.every(value => ['propext', 'Quot.sound'].includes(value)), name);
    const candidate = inventory.milestoneCandidates.find(item => item.name === name);
    assert.equal(MilestoneTheoremKernelTypeSha2560(name, candidate.kernelType), hash, name);
    assert.equal(map.earnedMilestoneTheoremKernelTypeSha256[name], hash, name);
  }
});

test('M278 compiled interface: weakening or supplying a conclusion cannot retain credit', async () => {
  const {inventory, map, sourceClosure} = await sources0();
  const alternatives = new Map();
  for (const [name, hash] of REVIEWED) {
    const current = inventory.milestoneCandidates.find(row => row.name === name).kernelType;
    const changed = [
      'Lean.Expr.const ' + String.fromCharCode(96) + 'True []',
      'Lean.Expr.forallE ' + String.fromCharCode(96) + 'supplied (' + current + ') (' + current + ') (Lean.BinderInfo.default)',
    ];
    for (const type of changed) assert.notEqual(MilestoneTheoremKernelTypeSha2560(name, type), hash, name);
    alternatives.set(name, changed);
  }
  // Check every pin cheaply above; exercise the large publication boundary at
  // the whole-carrier reconstruction, exact conservation and checked strict descent.
  for (const name of [
    'PNP.DirectWire.ClosedSupportFullGain.result_fullEquivalent',
    'PNP.DirectWire.ClosedSupportFullGain.result_gain_balance',
    'PNP.DirectWire.ClosedSupportFullGain.improvement?_strictGain',
  ]) for (const kernelType of alternatives.get(name)) {
    const mutation = {...inventory, milestoneCandidates: inventory.milestoneCandidates.map(row =>
      row.name === name ? {...row, kernelType} : row)};
    const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
    assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false, name);
    assert.equal(result.gate.passed, false);
  }
});

test('M278 compiled interface: missing evidence, added authority and widened scope reject', async () => {
  const {inventory, inventoryBytes, map, sourceClosure} = await sources0();
  const name = 'PNP.DirectWire.ClosedSupportFullGain.result_gain_balance';
  const addAuthority = row => row.name === name
    ? {...row, axioms: ['PNP.UnauthorizedAuthority', 'Quot.sound', 'propext']} : row;
  const mutation = {...inventory, declarations: inventory.declarations.map(addAuthority),
    milestoneCandidates: inventory.milestoneCandidates.map(addAuthority)};
  const result = DeriveFormalPublication0(mutation, map, canonical0(mutation), sourceClosure);
  assert.equal(result.milestones.find(row => row.id === MILESTONE.id).earned, false);
  assert.equal(result.gate.passed, false);
  const missing = {...inventory, milestoneCandidates: inventory.milestoneCandidates.filter(row => row.name !== name)};
  assert.throws(() => DeriveFormalPublication0(missing, map, canonical0(missing), sourceClosure),
    /reviewed milestone theorem candidate inventory mismatch/u);
  for (const field of ['scope', 'nonClaim']) {
    const widened = {...map, milestones: map.milestones.map(row => row.id === MILESTONE.id
      ? {...row, [field]: 'Computed reference savings automatically yield proper-positive supports, global route completeness, unconditional ZeroSlack and polynomial minimization.'} : row)};
    assert.throws(() => DeriveFormalPublication0(inventory, widened, inventoryBytes, sourceClosure),
      /map drifted from the reviewed specification/u);
  }
  const changedPin = {...map, earnedMilestoneTheoremKernelTypeSha256: {
    ...map.earnedMilestoneTheoremKernelTypeSha256, [name]: '0'.repeat(64)}};
  assert.throws(() => DeriveFormalPublication0(inventory, changedPin, inventoryBytes, sourceClosure),
    /map drifted from the reviewed specification/u);
});

const META = {
  "coordinate": "PNP-FORMAL-RECONSTRUCTION-STATUS-2026-09-19-278",
  "doc": "docs/lean_closed_support_full_gain.md",
  "plan": "docs/plans/2026-09-19-computed-closed-support-full-profile-gain.md",
  "audit": "lean-audit/PNPClosedSupportFullGainAxiomAudit.lean",
  "testFiles": [
    "audits/lean-closed-support-full-gain0.test.mjs",
    "audits/lean-closed-support-full-gain-publication0.test.mjs"
  ],
  "command": "node --test audits/lean-closed-support-full-gain0.test.mjs audits/lean-closed-support-full-gain-publication0.test.mjs",
  "workflowCommands": "set -euo pipefail\nnode scripts/check-lean-axioms.mjs lean-audit/PNPClosedSupportFullGainAxiomAudit.lean\nlake env lean -DwarningAsError=true --run lean-regression/PNPClosedSupportFullGain.lean\n",
  "publicationDecision": "Publication decision: defer. This completes the physical reconstruction of a computational-field-preserving finite reference improvement, not proper-positive support discovery, complete manuscript profiles, terminal-derived families, global route coverage or polynomial construction. No fixed weighted checkpoint or global gate changes, and the public global-proof bottom line remains unchanged. Preserve the coherent M264 website pin and batch pending core evidence at the next major publication.",
  "regressionCommands": [
    "lake env lean -DwarningAsError=true --run lean-regression/PNPClosedSupportFullGain.lean"
  ],
  "statusFields": {
    "leanClosedSupportFullGainFormalized": true,
    "leanClosedSupportFullGainAxiomAuditPassed": true,
    "leanClosedSupportFullGainAuditedDeclarationCount": 27,
    "leanClosedSupportFullGainPrimaryInputSpecializationTheorem": "PNP.DirectWire.ClosedSupportFullGain.prefixSource_value",
    "leanClosedSupportFullGainRetainedFieldTheorem": "PNP.DirectWire.ClosedSupportFullGain.prefixField_value",
    "leanClosedSupportFullGainWholeCarrierTheorem": "PNP.DirectWire.ClosedSupportFullGain.result_fullEquivalent",
    "leanClosedSupportFullGainExactGateBalanceTheorem": "PNP.DirectWire.ClosedSupportFullGain.result_exact_accounting",
    "leanClosedSupportFullGainWholeFullSlackBalanceTheorem": "PNP.DirectWire.ClosedSupportFullGain.result_fullSlack_balance",
    "leanClosedSupportFullGainLocalSlackBoundTheorem": "PNP.DirectWire.ClosedSupportFullGain.localFullSlack_le_global",
    "leanClosedSupportFullGainCheckedRouteTheorem": "PNP.DirectWire.ClosedSupportFullGain.improvement?_sound",
    "leanClosedSupportFullGainStrictGainTheorem": "PNP.DirectWire.ClosedSupportFullGain.improvement?_strictGain",
    "leanClosedSupportFullGainArbitraryFiniteDimensionsCovered": true,
    "leanClosedSupportFullGainComputedClosedSupportAndFullMinimum": true,
    "leanClosedSupportFullGainComplementAndReconnectionDerived": true,
    "leanClosedSupportFullGainUniformOutputsAndComputationalFieldsPreserved": true,
    "leanClosedSupportFullGainCallerSuppliedObserverReplacementOrCorrectnessRequired": false,
    "leanClosedSupportFullGainLocalFullSlackExactlyRetiredFromWhole": true,
    "leanClosedSupportFullGainProperPositiveSupportDiscoveryProved": false,
    "leanClosedSupportFullGainWholeSpanIsProperLocalVerifyDW": false,
    "leanClosedSupportFullGainCompleteManuscriptProfileGrammarProved": false,
    "leanClosedSupportFullGainGlobalRouteCoverageProved": false,
    "leanClosedSupportFullGainUnconditionalSaturatePositiveProved": false,
    "leanClosedSupportFullGainUnconditionalBCELReadyProved": false,
    "leanClosedSupportFullGainUnconditionalZeroSlackProved": false,
    "leanClosedSupportFullGainExactPolynomialPCCMinProved": false,
    "leanClosedSupportFullGainPolynomialRuntimeOutputAndCertificateBoundsProved": false,
    "leanClosedSupportFullGainReferenceMinimumMatchingAndInfluenceAreExhaustive": true,
    "leanClosedSupportFullGainRuntimeExecutionIsProofAuthority": false,
    "leanClosedSupportFullGainScope": "arbitrary-finite-computed-closed-support-full-minimum-derived-physical-complement-uniform-whole-output-and-computational-field-equivalence-exact-gate-and-full-slack-balance-checked-strict-descent-no-proper-positive-discovery-complete-profile-global-route-or-polynomial-claim"
  }
};
const prose0 = value => value.replaceAll('**', '').replace(/\s+/gu, ' ').trim();
async function release0() {
  const [statusText, progressText] = await Promise.all([
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'), text0('status/PROOF_PROGRESS.json'),
  ]);
  return {status: JSON.parse(statusText), progress: JSON.parse(progressText)};
}

test('M278 release preflight: package, exact workflow and status commands share one interface', async () => {
  const [pkg, surface, verifier, workflow, statusSource, statusText] = await Promise.all([
    text0('package.json'), text0('pcc-formal-public-surface0.mjs'), text0('scripts/pnp-verify-all.mjs'),
    text0('.github/workflows/lean-bridge.yml'), text0('pcc-formal-reconstruction-status0.mjs'),
    text0('status/FORMAL_RECONSTRUCTION_STATUS.json'),
  ]);
  assert.equal(JSON.parse(pkg).scripts['audit:m278'], META.command);
  assert.ok(surface.includes("'audit:m278': '" + META.command + "'"));
  for (const file of META.testFiles) assert.ok(verifier.includes("'" + file + "'"), file);
  assert.ok(workflow.includes('run: npm run audit:m278'));
  const steps = workflow.split(/^      - name:/mu).filter(step =>
    step.includes('node scripts/check-lean-axioms.mjs ' + META.audit));
  assert.equal(steps.length, 1);
  const block = steps[0].split('        run: |\n')[1];
  assert.ok(block);
  assert.equal(block.trimEnd().split('\n').map(line => line.slice(10)).join('\n') + '\n', META.workflowCommands);
  const status = JSON.parse(statusText);
  for (const command of [
    'npm run audit:m278', 'node scripts/check-lean-axioms.mjs ' + META.audit,
    ...META.regressionCommands,
  ]) assert.ok(status.verificationCommands.includes(command), command);
  for (const field of Object.keys(META.statusFields))
    assert.equal(statusSource.split(field + ':').length - 1, 2, field);
});

test('M278 release: status pins the exact bounded claims and rejects every changed field', async () => {
  const {status} = await release0();
  for (const [field, value] of Object.entries(META.statusFields)) {
    assert.deepEqual(status[field], value, field);
    const mutation = {...status, [field]: typeof value === 'boolean' ? !value :
      typeof value === 'number' ? value + 1 : value + ':unreviewed'};
    const result = await CheckFormalReconstructionStatus0({writeOutput: false, statusOverride: mutation, siteOverride: mutation});
    assert.equal(result.tag, 'reject', field);
    assert.equal(result.coord, 'FormalReconstructionStatus.Field', field);
    assert.deepEqual(result.path, ['status/FORMAL_RECONSTRUCTION_STATUS.json', field], field);
  }
});

test('M278 release: computed full-profile physical gain earns no unconditional checkpoint', async () => {
  const {status, progress} = await release0(), {inventory} = await sources0();
  assert.equal(validateProofProgress0(progress, status, inventory).tag, 'accept');
  const reviews = progress.history.filter(row => row.asOfCoordinate === META.coordinate);
  assert.equal(reviews.length, 1);
  const review = reviews[0];
  assert.equal(review.scoreChanged, false);
  assert.deepEqual(review.changedCheckpointIds, []);
  assert.deepEqual(review.changeRecords, []);
  assert.equal(review.riskWeightedProofCompletionPercent, 40);
  assert.equal(review.uncertaintyLowPercent, 20);
  assert.equal(review.uncertaintyHighPercent, 40);
  assert.equal(review.globalGatesClosed, 0);
  assert.equal(review.globalGatesAvailable, 5);
  assert.ok(prose0(review.rationale).includes('No fixed load-bearing checkpoint changes state'));
  if (progress.asOfCoordinate !== META.coordinate) return;
  assert.deepEqual(review.formalArtefactCoverage, {
    earnedRows: status.formalPublicationMilestones.filter(row => row.earned).length,
    totalRows: status.formalPublicationMilestones.length,
  });
  assert.deepEqual(progress.tracks.map(track => track.pointsEarned), [13, 20, 2, 1, 4]);
  assert.equal(progress.proofCompletion.percent, 40);
  assert.equal(progress.globalGates.length, 5);
  assert.ok(progress.globalGates.every(gate => gate.status === 'open'));
  assert.deepEqual(inventory.projectAxioms, []);
  assert.deepEqual(progress.projectSpecificAxiomsRemaining, []);
  assert.equal(inventory.declarations.some(row => row.name === 'PNP.Main.p_eq_np'), false);
  assert.equal(status.leanConcreteCNFSATInPFormalized, false);
  assert.equal(status.concretePublicationGate.passed, false);
  assert.equal(progress.publicationGate.passed, false);
  assert.deepEqual(progress.rootTheorem, {name: 'PNP.Main.p_eq_np', present: false, built: false, axiomAuditPassed: false});
  const inflated = structuredClone(progress);
  inflated.proofCompletion.pointsEarned += 1;
  inflated.proofCompletion.percent += 1;
  assert.throws(() => validateProofProgress0(inflated, status, inventory),
    error => error.code === 'ProofCompletion.StoredEarned');
});

test('M278 release: every current summary and FAQ uses the canonical independent metrics', async () => {
  const {progress} = await release0();
  const doc = prose0(await text0(META.doc)), plan = prose0(await text0(META.plan));
  assert.ok(doc.includes(META.coordinate));
  assert.ok(doc.includes(prose0(MILESTONE.scope)));
  assert.ok(doc.includes(prose0(MILESTONE.nonClaim)));
  assert.ok(doc.includes(prose0(META.publicationDecision)));
  assert.ok(plan.includes('Publication decision: defer'));
  if (progress.asOfCoordinate !== META.coordinate) return;
  const p = progress.proofCompletion, a = progress.formalArtefactCoverage;
  const metrics = [
    'Formal artefact coverage: ' + a.earnedRows + ' of ' + a.totalRows + ' current scoped publication rows earned.',
    'Risk-weighted proof completion estimate: ' + p.percent + '%.',
    'Uncertainty range: ' + p.uncertaintyLowPercent + '% to ' + p.uncertaintyHighPercent + '%.',
    'Global gates closed: ' + progress.globalGates.filter(gate => gate.status === 'closed').length + ' of 5.',
  ];
  for (const file of ['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
    'docs/proof_pipeline.md', 'docs/audit_questions.md', 'docs/proof_progress.md', META.doc]) {
    const text = await text0(file), current = prose0(text);
    for (const metric of metrics) assert.ok(current.includes(metric), file + ': ' + metric);
    if (file === 'docs/proof_progress.md') {
      const currentIntro = prose0(text.split('## Risk-weighted proof completion estimate')[0]);
      for (const metric of metrics) assert.ok(currentIntro.includes(metric), file + ': current introduction ' + metric);
      assert.ok(currentIntro.includes(META.coordinate));
    }
    if (file === 'README.md') {
      const row = text.split('\n').find(line => line.startsWith('| **How is progress measured?** |'));
      assert.ok(row);
      for (const metric of metrics) assert.ok(prose0(row).includes(metric), 'FAQ: ' + metric);
      const boundary = text.split('\n').find(line => line.startsWith('| **What is the current verification status?** |'));
      assert.ok(boundary?.includes('M278'));
      assert.ok(boundary.includes('global route coverage'));
    }
    if (['README.md', 'docs/FORMAL_RECONSTRUCTION.md', 'docs/lean_bridge.md',
      'docs/proof_pipeline.md', 'docs/audit_questions.md'].includes(file)) {
      const region = text.split('<!-- M278-CURRENT-SUMMARY:BEGIN -->')[1]?.split('<!-- M278-CURRENT-SUMMARY:END -->')[0];
      assert.ok(region, file + ': current summary');
      for (const metric of metrics) assert.ok(prose0(region).includes(metric), file + ': summary ' + metric);
      assert.doesNotMatch(region, /\d+[ -]pages?|PDF[^\n]*page count/iu);
    }
  }
  const report = await text0('canonical_proof_report.tex');
  const cover = prose0(report.split('\\end{titlepage}')[0]);
  assert.doesNotMatch(cover, /Latest earned evidence:/u);
  assert.ok(cover.includes('Formal artefact coverage: ' + a.earnedRows + ' of ' + a.totalRows));
  assert.ok(cover.includes('Risk-weighted proof completion estimate: ' + p.percent + ' percent.'));
});
